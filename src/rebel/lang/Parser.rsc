module rebel::lang::Parser

import rebel::lang::Syntax;

import ParseTree;
import String;

Module parseModule(loc file) = parse(#start[Module], replaceProjectScheme(file), allowAmbiguity=false).top;
Module parseModule(str x, loc file) = parse(#start[Module], x, replaceProjectScheme(file), allowAmbiguity=false).top;

loc replaceProjectScheme(loc file) {
  if (file.scheme == "home") { 
    return file;
  } else if (file.scheme == "project") {
    loc base = file;
    while (!(endsWith(base.path, "examples") || endsWith(base.path, "src"))) {
      base = base.parent; 
    }
    base = base.parent; // last time

    return |home:///workspace/rebel2/| + replaceFirst(file.path, base.path, ""); 
  } else {
    throw "Unable to build correct location";
  } 
}
