@license{
  Copyright (c) Tijs van der Storm <Centrum Wiskunde & Informatica>.
  All rights reserved.
  This file is licensed under the BSD 2-Clause License, which accompanies this project
  and is available under https://opensource.org/licenses/BSD-2-Clause.
}
@contributor{Tijs van der Storm - storm@cwi.nl - CWI}

module salix::lib::REPL

import salix::lib::XTerm;
import salix::App;
import salix::Core;
import salix::HTML;

import util::Maybe;
import List;
import IO;
import String;


alias REPLModel = tuple[
  str id,
  str prompt,
  list[str] history,
  int pointer,
  str currentLine,
  list[str] completions,
  int cycle
];

REPLModel initRepl(str id, str prompt) {
  do(write(noOp(), id, prompt));
  return <id, prompt, [], 0, "", [], -1>;
} 
  
data Msg
  = xtermData(str s)
  | noOp()

  // allow container to capture a message; in a fully typed way this would
  // make REPLMsg parametric on the parent message typed:
  //  REPLMsg[&P] = parent(&P msg)
  // the container would wrap as follows
  // data Msg = ... | repl(REPLMsg[Msg] arg)
  
  | parent(Msg msg) 
  ;
  
REPLModel replaceLine(REPLModel model, str newLine, Maybe[str](str) hl) {
  writeLine(model, newLine, hl);
  // NB: writeLine needs access to old line, so update after it.
  return model[currentLine=newLine];
} 

void writeLine(REPLModel model, str newLine, Maybe[str](str) hl) {
  str zap = ( "\r" | it + " " | int _ <- [0..size(model.currentLine) + size(model.prompt)] );
  if (just(str highlighted) := hl(newLine)) {
    newLine = highlighted;
  }
  do(write(noOp(), model.id, "<zap>\r<model.prompt><newLine>"));
}

// repl updater generator (for use in mapCmds)
REPLModel(Msg, REPLModel) replUpdate(tuple[Msg, str](str) eval, list[str](str) complete, Maybe[str](str) highlight) 
  = REPLModel(Msg msg, REPLModel rm) {
      return replUpdate(eval, complete, highlight, msg, rm);
    };

REPLModel replUpdate(tuple[Msg, str](str) eval, list[str](str) complete, Maybe[str](str) highlight, Msg msg, REPLModel model) {
  
  switch (msg) {
  
    case xtermData(str s): {
      if (s != "\t") {
        model.cycle = -1; // exit cycle mode
      }
      if (s == "\r") {
        <evalMsg, result> = eval(model.currentLine);
        do(write(parent(evalMsg), model.id, "\r\n<result>\r\n<model.prompt>"));
        model.history += [model.currentLine];
        model.pointer = size(model.history);
        model.currentLine = "";
      }
      else if (s == "\a7f") { 
        if (model.currentLine != "" ) {
          model.currentLine = model.currentLine[0..-1];
          do(write(noOp(), model.id, "\b \b"));
        }
      }
      else if (s == "\a1b[A") { // arrow up
        if (model.pointer > 0) {
          model.pointer -= 1;
          model = replaceLine(model, model.history[model.pointer], highlight); 
        }
      }
      else if (s == "\a1b[B") { // arrow down
        if (model.pointer < size(model.history) - 1) {
	        model.pointer += 1;
	        model = replaceLine(model, model.history[model.pointer], highlight);
        }
      }
      else if (s == "\t") {
        if (model.cycle == -1) {
          model.completions = complete(model.currentLine);
        }
        if (model.cycle < size(model.completions) - 1) {
          model.cycle += 1;
        }
        else {
          model.cycle = 0;
        }
        str comp = model.completions[model.cycle];
        model = replaceLine(model, model.completions[model.cycle], highlight);
      }
      else {
        model.currentLine += s;
        if (just(str x) := highlight(model.currentLine)) {
          writeLine(model, x, highlight);
        }
        else {
          do(write(noOp(), model.id, s));
        }
      }
    }
  }
  
  return model;
}  

// render a REPL
void repl(Msg(Msg) f, REPLModel m, str id, value vals...) 
  = mapView(f, m, repl(id, vals));

// repl view generator (helper)
void(REPLModel) repl(str id, value vals...) 
  =  void(REPLModel m) { xterm(id, [onData(xtermData)] + vals); }; 

