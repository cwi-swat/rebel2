@license{
  Copyright (c) Tijs van der Storm <Centrum Wiskunde & Informatica>.
  All rights reserved.
  This file is licensed under the BSD 2-Clause License, which accompanies this project
  and is available under https://opensource.org/licenses/BSD-2-Clause.
}
@contributor{Tijs van der Storm - storm@cwi.nl - CWI}

module salix::lib::Highlight

import salix::HTML;
import ParseTree;
import IO;
import String;

public map[str, lrel[str, str]] cat2styles = (
  "Type": [<"color", "#748B00">],
  "Identifier": [<"color", "#485A62">],
  "Variable": [<"color", "#268BD2">],
  "Constant": [<"color", "#CB4B16">],
  "Comment": [<"font-style", "italic">, <"color", "#8a8a8a">],
  "Todo": [<"font-weight", "bold">, <"color", "#af0000">],
//  "Focus": [<"border", "1px">, <"border-style", "solid">],
  "MetaAmbiguity": [<"color", "#af0000">, <"font-weight", "bold">, <"font-style", "italic">],
  "MetaVariable": [<"color", "#0087ff">],
  "MetaKeyword": [<"color", "#859900">],
  "StringLiteral": [<"color", "#2AA198">]
);



alias MoreCSS = lrel[str,str](Tree);

lrel[str,str] noMore(Tree t) = [];

// TODO: don't do more CSS, but have map[loc, lrel[str,str]] or something
// to have general semantic styling
// also have a map links map[loc, tuple[str class, str href]];
// and insert <a class="class" href="href">...</a>

void highlightToHtml(Tree t, void(list[value]) container = pre, map[str,lrel[str,str]] cats = cat2styles, 
  int tabSize = 2, MoreCSS more = noMore) {
  container([() {
    str pending = highlightRec(t, "", cats, tabSize, more);
    if (pending != "") {
      text(pending);
    }
  }]);
}

private str highlightRec(Tree t, str current, map[str, lrel[str, str]] cats, int tabSize, MoreCSS more) {
  
  void highlightArgs(list[Tree] args) {
    for (Tree a <- args) {
      current = highlightRec(a, current, cats, tabSize, more);
    }
  }
  
  void commitPending() {
    if (current != "") {
      text(current);
    }
    current = "";
  }
  
  switch (t) {
    case appl(prod(lit(/^<s:[a-zA-Z_0-9]+>$/), _, _), list[Tree] args): {
      commitPending();
      span(class("MetaKeyword"), style(cats["MetaKeyword"]), s);
    }

    case appl(prod(Symbol d, list[Symbol] ss, set[Attr] as), list[Tree] args): {
      if (\tag("category"(str cat)) <- as, cat in cats) {
        commitPending();
        span(class(cat), style(cats[cat] + more(t)), () {
          highlightArgs(args);
          commitPending();
        });  
      }
      else if (more(t) != []) {
        commitPending();
        span(style(more(t)), () {
          highlightArgs(args);
          commitPending();
        });  
      }
      else {
        highlightArgs(args);
      }
    }
    
    case appl(_, list[Tree] args):
      highlightArgs(args);
    
    case char(int c): {
      str s = stringChar(c);
      current += s == "\t" ? ("" | it + " " | _ <- [0..tabSize]) : s;
    }
    
    case amb(set[Tree] alts): {
      if (Tree a <- alts) {
        current = highlightRec(a, current, cats, more);
      }
    }
  
  }
  
  return current;
    
} 

private map[str, str] cat2ansi = (
  "Type": "",
  "Identifier": "",
  "Variable": "",
  "Constant": "\u001B[0;36m", //cyan
  "Comment":  "\u001B[0;37m", // gray
  "Todo": "",
  "MetaAmbiguity": "\u001B[1;31m", // bold red
  "MetaVariable": "",
  "MetaKeyword": "\u001B[1;35m", // bold purple
  "StringLiteral": "\u001B[0;36m" // cyan
);


str highlightToAnsi(Tree t, map[str,str] cats = cat2ansi, int tabsize = 2) { 

  str reset = "\u001B[0m";
  
  str highlightArgs(list[Tree] args) 
    = ("" | it + highlightToAnsi(a, cats, tabsize) | Tree a <- args );
  
  switch (t) {
    
    case appl(prod(lit(/^<s:[a-zA-Z_0-9]+>$/), _, _), list[Tree] args): {
      return "<cats["MetaKeyword"]><s><reset>";
    }

    case appl(prod(Symbol d, list[Symbol] ss, set[Attr] as), list[Tree] args): {
      if (\tag("category"(str cat)) <- as) {
        // categories can't be nested, so just yield the tree.
        return "<cats[cat]><t><reset>";
      }
      return highlightArgs(args);
    }
    
    case appl(_, list[Tree] args):
      return highlightArgs(args);
    
    case char(int c): { 
      str s = stringChar(c);
      return  s == "\t" ? ("" | it + " " | _ <- [0..tabSize]) : s;
    }
    
    case amb(set[Tree] alts): {
      if (Tree a <- alts) {
        return highlightToAnsi(a, cats);
      }
    }

  }
  
  return "";
    
} 



