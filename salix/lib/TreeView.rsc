module salix::lib::TreeView

//https://github.com/jonmiles/bootstrap-treeview

import salix::Node;
import salix::Core;

import lang::json::IO;
import List;
import IO;


// Attributes to control state of tree node.
// TODO: these could be passed back upon events.
Attr checked() = attr("checked", "true");
Attr disabled() = attr("disabled", "true");
Attr expanded() = attr("expanded", "true");
Attr selected() = attr("selected", "true"); // same as HTML?

// Attributes to control appearance of a treenode
// NB: if id(str) isn't given, the text argument of a T
// will be used as the identifier of the node.
Attr icon(str glyph) = attr("icon", glyph);
Attr selectedIcon(str glyph) = attr("selectedIcon", glyph);
Attr color(str color) = attr("color", color);
Attr backColor(str color) = attr("backColor", color);
Attr href(str uri) = attr("href", uri); // same as HTML?
Attr selectable(bool b) = attr("selectable", "<b>");

// todo: make this reliable
Attr tags(list[str] ts) = attr("tags", intercalate("|", ts));

// The following attrs and events are interpreted as options to the treeview.
Attr backColor(str color) = attr("backColor", color);
Attr borderColor(str color) = attr("borderColor", color);
Attr checkedIcon(str glyph) = attr("checkedIcon", glyph);
Attr collapseIcon(str glyph) = attr("collapseIcon", glyph);
Attr color(str color) = attr("color", color);
Attr emptyIcon(str glyph) = attr("emptyIcon", glyph);
Attr enableLinks() = attr("enableLinks", "true");
Attr expandIcon(str glyph) = attr("expandIcon", glyph);
Attr highlightSearchResults(bool b) = attr("highlightSearchResults", "<b>");
Attr highlightSelected(bool b) = attr("highlightSelected", "<b>");
Attr levels(int n) = attr("levels", "<n>");
Attr multiSelect() = attr("multiSelect", "true");
Attr nodeIcon(str glyph) = attr("nodeIcon", glyph);
Attr onhoverColor(str color) = attr("onhoverColor", color);
Attr selectedIcon(str glyph) = attr("selectedIcon", glyph);
//Attr searchResultBackColor(str color) = attr("searchResultBackColor", color);
//Attr searchResultColor(str color) = attr("searchResultColor", color);
Attr selectedBackColor(str color) = attr("selectedBackColor", color);
Attr selectedColor(str color) = attr("selectedColor", color);
Attr showBorder(bool b) = attr("showBorder", "<b>");
Attr showCheckbox() = attr("showCheckbox", "true");
Attr showIcon(bool b) = attr("showIcon", "<b>");
Attr showTags() = attr("showTags", "true");
Attr uncheckedIcon(str glyph) = attr("uncheckedIcon", glyph);

Attr onNodeChecked(Msg(str) tn2msg) = event("nodeChecked", handler("node", encode(tn2msg)));
Attr onNodeCollapsed(Msg(str) tn2msg) = event("nodeCollapsed", handler("node", encode(tn2msg)));
Attr onNodeDisabled(Msg(str) tn2msg) = event("nodeDisabled", handler("node", encode(tn2msg)));
Attr onNodeEnabled(Msg(str) tn2msg) = event("nodeEnabled", handler("node", encode(tn2msg)));
Attr onNodeExpanded(Msg(str) tn2msg) = event("nodeExpanded", handler("node", encode(tn2msg)));
Attr onNodeSelected(Msg(str) tn2msg) = event("nodeSelected", handler("node", encode(tn2msg)));
Attr onNodeUnchecked(Msg(str) tn2msg) = event("nodeUnchecked", handler("node", encode(tn2msg)));
Attr onNodeUnselected(Msg(str) tn2msg) = event("nodeUnselected", handler("node", encode(tn2msg)));

Msg parseMsg(str id, "nodeId", Handle h, map[str, str] p)
  = applyMaps(id, h, decode(id, h, #(Msg(str)))(p["node"]));

alias T = void(str text, list[value] vals);
alias TV = void(T);

private data _Tree
  = tree(str text, list[_Tree] nodes = [], map[str, str] attrs = ());

@doc{

TreeView ::= treeView(TVAttr*, TVBlock?)
TVAttr ::= (see above) | on(see above)  
TVBlock ::= (T t) {  TVNode* }
TVNode ::= t(str, NAttr*, NBlock?) // if id attribute is absent, the text arg is used as id
NBlock ::= () { TVNode* }
NAttr ::= (see above) | on(see above) 

}
void treeView(value vals...) {
  list[_Tree] stack = [tree("dummy")];
  
  _Tree top() = stack[-1];
  
  void push(_Tree t) {
    stack += [t];
  }
  
  _Tree pop() {
    _Tree t = top();
    stack = stack[0..-1];
    return t;
  }

  void t(str text, value vals...) {
    _Tree cur = tree(text);
    
    if (vals != [], void() block := vals[-1]) {
      push(cur);
      block();
      cur = pop();
    }
    
    map[str,str] attrs = attrsOf([ a | Attr a <- vals ]);
    if (attrs != ()) {
      cur.attrs = attrs;
    }
    stack = stack[0..-1] + stack[-1][nodes = stack[-1].nodes + [cur]];
  }
  
  if (vals != [], TV tv := vals[-1]) {
    tv(t);
  }
  
  build(vals, Node(list[Node] _, list[Attr] attrs) {
     return native("treeView", "treeView", attrsOf(attrs), (), eventsOf(attrs), extra = ("data": stack[0].nodes));
  });
}

