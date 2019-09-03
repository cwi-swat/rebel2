module lang::Parser

import lang::Syntax;

import ParseTree;
import IO;

Spec parseSpec(loc file) = parse(#start[Spec], file, allowAmbiguity=false).top;
Spec parseSpec(str x, loc file) = parse(#start[Spec], x, file, allowAmbiguity=false).top;
