module rebel::vis::salix::StateMachineCat

import salix::Core;
import salix::HTML;
import salix::Node;

import List;
import IO;

void stateMachineCat(str id, str smCatModel, value vals...)
  = build(vals, Node(list[Node] _, list[Attr] attrs) { 
      return native("smCat", id, attrsOf(attrs), propsOf(attrs), eventsOf(attrs), extra = ("model": smCatModel));
    });
