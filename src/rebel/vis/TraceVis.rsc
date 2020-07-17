module rebel::vis::TraceVis

import rebel::checker::Trace;
import rebel::lang::Syntax; 
import rebel::checker::translation::CommonTranslationFunctions;
import rebel::vis::SpecToSalixConverter;

import salix::App;
import salix::HTML;
import rebel::vis::salix::StateMachineCat;

import List;
import IO;
import String;
import Type;
import Set; 

alias TraceVisModel = tuple[str check, Trace trace, int currentStep, int totalSteps, bool isInfiniteTrace, bool showNxt, map[str,Filter] filters]; 

data Msg 
  = nxt()
  | showNxt()
  | hideNxt()
  | prev()
  | changeFilter(str selected)
  | toggleConstants()
  ;

App[TraceVisModel] createTraceVis(str check, Trace trace) {
  TraceVisModel init() = <check, trace, 0, getTotalNumberOfSteps(trace), isInfiniteTrace(trace), false, initialFilters(trace)>;
    
  return webApp(makeApp("rebelTraceVis", init, view, update), 
    |project://rebel2/salix/tracevis.html|, |project://rebel2/salix/|
  );
}

bool isInfiniteTrace(Trace t) = /goalInfiniteTrace(_,_,_) := t;

map[str,Filter] initialFilters(Trace t) = (inst : show() | <_,inst> <- t.conf.instances<0,1>);
  
void view(TraceVisModel m) {
  div(() {
    h3("Found trace for check `<m.check>`");
    
    div(class("panel panel-default"), () {
      div(class("panel-body"), () {      
        ul(class("nav nav-tabs"), () {
          li(class("active"), () { 
            a(href("#visual"), attribute("data-toggle","tab"), () { span("Visual trace"); }); 
          });
          li(() { 
            a(href("#textual"), attribute("data-toggle","tab"), () { span("Textual trace"); }); 
          });        
        });
        
        div(class("tab-content"), () {
          div(attribute("role","tab-pane"), class("tab-pane active"),id("visual"), () { 
            displayVisualTrace(m);
          });
  
          div(attribute("role","tab-pane"), class("tab-pane"),id("textual"), () { 
            displayTextualTrace(m);
          });
          
        });
      });
    });
  });
}

void displayTextualTrace(TraceVisModel m) {
  textarea(id("textual_trace"), trace2Str(m.trace));
}

void displayVisualTrace(TraceVisModel m) {
  Trace currentStep = currentStep(m);

  str stepHeading() = "Initial state (<m.totalSteps> steps total)" when m.currentStep == 0; 
  str stepHeading() = "Step <m.currentStep> (out of <m.totalSteps>)" when m.currentStep > 0, m.currentStep < m.totalSteps;
  str stepHeading() = "Goal state" when m.currentStep == m.totalSteps;
  
  str nxtButtonLabel() = "back to step <backToStep>" when goalInfiniteTrace(_,_,int backToStep) := currentStep;
  str nxtButtonLabel() = "next";
  
  bool disableNext() = false when goalInfiniteTrace(_,_,_) := currentStep; 
  default bool disableNext() = m.currentStep == m.totalSteps;
  
  p(() {
    h4(stepHeading());
    
    p(class("btn-toolbar"), () { 
      button(\type("button"), onClick(prev()), class("btn btn-secondary"), disabled(m.currentStep == 0), "previous");
      button(\type("button"), onClick(nxt()), class("btn btn-primary"), disabled(disableNext()), onMouseEnter(showNxt()), onMouseLeave(hideNxt()), nxtButtonLabel());
      
      button(\type("button"), class("btn btn-link"), attribute("data-toggle", "collapse"), attribute("data-target", "#displayoptions"), attribute("aria-expanded","false"), attribute("aria-controls", "displayoptions"), () {
        span(class("glyphicon glyphicon-cog"), attribute("aria-hidden","true"));
        text("Display options");
      });
    });
    
    div(class("collapse"), id("displayoptions"), () {
      p(class("alert alert-info"), attribute("role", "alert"), () {
        displayFiltersAndOptions(m);
      });
    });
    
  });
  p(() {  
    displayNextEvent(m);
  });
    
  div(style(("overflow":"scroll")), () {
    stateMachineCat("rebelVis", displayConf(m), style(("max-width":"900pt")));
  });
}

void displayFiltersAndOptions(TraceVisModel m) {
  form(class("form-inline"), () {
    for (str inst <- m.filters) {
      div(class("form-group"), () {
        label(\for("<inst>"),"<inst>");
        select(class("form-control"), id("<inst>"), onChange(changeFilter), () {
          option(selected(m.filters[inst] == show()), \value("<inst>§show"), "Show");
          option(selected(m.filters[inst] == valuesOnly()), \value("<inst>§valuesOnly"), "Values only");
          option(selected(m.filters[inst] == hide()), \value("<inst>§hide"), "Hide");
        });
      });
    }
    div(class("form-group"), () {
      button(\type("button"), onClick(toggleConstants()), class("btn btn-primary"),"Hide/show constants");
    });
  });
}

Trace currentStep(TraceVisModel m) = (m.trace | it.next | int _ <- [0..m.currentStep]);

void displayNextEvent(TraceVisModel m) {
  Trace currentStep = currentStep(m);

  blockquote(() { 
    p(() { 
      if (m.currentStep != m.totalSteps || goalInfiniteTrace(_,_,int backToStep) := currentStep) {
        text("Step <m.currentStep+1>: ");
        
        code(() {
          strong("<currentStep.re.instance>");
          text(".<currentStep.re.event.name>(");
          
          int i = 1;
          for (<param,val> <- currentStep.re.arguments) {
            var("<param>");
            text("=");
            kbd(val);
            if (i < size(currentStep.re.arguments)) {
              text(", ");
            }
            i += 1;
          }
          
          text(")");
        });
      } else {
        text("-");
      }
    });
  });
}

int getTotalNumberOfSteps(Trace t) {
  int total = 0;
  
  while (t has next) {
    t = t.next;
    total += 1;
  } 

  return total;
}

TraceVisModel update(Msg msg, TraceVisModel m) {
  Trace currentStep = currentStep(m);
  
  switch (msg) {
    case nxt(): {
      if (goalInfiniteTrace(_,_,int backToStep) := currentStep) {    
        m.currentStep = backToStep-1;
      } else {
        m.currentStep += 1;
      }
    }
    case prev(): {
      m.currentStep -= 1;
      m.showNxt = false;
    }
    case showNxt(): m.showNxt = true;
    case hideNxt(): m.showNxt = false;
    case changeFilter(str selected): {
      list[str] vals = split("§", selected);
      m.filters[vals[0]] = make(#Filter, vals[1], []);
    }
    case toggleConstants(): {
      for (str s <- m.filters, s == toUpperCase(s)) {
        m.filters[s] = hide();
      }
    }
  }
  
  return m;
}

//data Configuration 
//  = config(rel[Spec spc, str instance, State state] instances, rel[Spec spc, str instance, str field, str val] values)
//  ;

//data Trace
//  = step(Configuration conf, RaisedEvent re, Trace next)
//  | goal(Configuration conf)
//  | goalInfiniteTrace(Configuration conf, RaisedEvent re, int backTo)
//  ;
//
//
//data RaisedEvent
//  = raisedEvent(Spec spc, Event event, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
//  | raisedEventVariant(Spec spc, Event event, str eventName, str variant, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
//  ;


str displayConf(TraceVisModel m) {
  Trace currentStep = (m.trace | it.next | int _ <- [0..m.currentStep]);
  
  str getVals({str val}) = val;
  default str getVals(set[str] vals) = "<intercalate(" ", toList(vals))>";
  
  map[str,str] getValues(Spec spc, str inst) = (field : getVals(currentStep.conf.values[spc][inst][field]) | field <- currentStep.conf.values[spc][inst]<0>);
  
  str getEventName(str inst) = currentStep.re has eventName 
    ? "<currentStep.re.eventName>::<currentStep.re.variant>"
    : "<currentStep.re.event.name>"
    when currentStep has re, inst == currentStep.re.instance;
  default str getEventName(str inst) = "";   
  
  str getNxtTrans(str inst) = m.showNxt ? getEventName(inst) : "";
  
  bool hasFields(Spec s) = /Fields _ := s.fields;
  
  str affectedInstanceColor(str inst) = "color=\"red\"" when m.showNxt, currentStep has re, inst in currentStep.re.affectedInstances;
  default str affectedInstanceColor(str inst) = "";
  
  list[str] machines = [];
  for (Spec spc <- currentStep.conf.instances<0>, <str inst, State cur> <- currentStep.conf.instances[spc], m.filters[inst] != hide()) {
    str newMach = specToStateMachineJs(spc, instance = inst, activeState = state2Str(cur), showValues = hasFields(spc), values = getValues(spc, inst), nextTrans = getNxtTrans(inst), \filter = m.filters[inst]);
    machines += "<inst>[Label=\"<inst> \<\<<spc.name>\>\>\" <affectedInstanceColor(inst)>]<if (newMach != "") {>{<newMach>}<}>";
  }
  str result = "parallel[Label=\"\<\<Composite Machine\>\>\"] {
               '  <intercalate(",", machines)>;
               '};";
  
  return result;
}

private str state2Str(State::uninitialized()) = "initial";
private str state2Str(State::finalized())     = "final";
private str state2Str(State::state(str name)) = name;
private str state2Str(State::anyState())      = "";
private str state2Str(State::noState())       = "";


