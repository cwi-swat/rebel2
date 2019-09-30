module lang::Parser

import lang::Syntax;

import ParseTree;
import IO;

Module parseModule(loc file) = parse(#start[Module], file, allowAmbiguity=false).top;
Module parseModule(str x, loc file) = parse(#start[Module], x, file, allowAmbiguity=false).top;
