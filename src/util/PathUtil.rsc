module util::PathUtil

import String;
import IO;
import ParseTree;
import util::Maybe;

import rebel::lang::Syntax;

data PathConfig = pathConfig(list[loc] srcs = [], loc tmodels = |unknown:///|, loc normalized = |unknown:///|, loc checks = |unknown:///|);

loc project(loc file) {
   assert file.scheme == "project";
   return |project://<file.authority>|;
}

PathConfig defaultPathConfig(loc file) {
  //if (file.scheme != "project") {
  //  throw "Can only create default path config for files with `project` scheme";
  //}
  //
  //loc proj = project(file);
  loc proj = |home:///workspace/rebel2|;
  return pathConfig(srcs = [proj + "src", proj + "examples"], tmodels = proj + "bin/tm", normalized = proj + "bin/normalized", checks = proj + "/bin/checks");
}

PathConfig normalizerPathConfig(loc file) {
  //if (file.scheme != "project") {
  //  throw "Can only create default path config for files with `project` scheme";
  //}
  //
  //loc proj = project(file);
  loc proj = |home:///workspace/rebel2|;
  return pathConfig(srcs = [proj + "bin/normalized"], tmodels = proj + "bin/normalized", normalized = proj + "bin/normalized");
}


loc extractBase(Module m) = extractBase(m.\module.name); 

loc extractBase(QualifiedName modDef) {
  loc modLoc = m@\loc.top;
  
  for (str part <- split("::", "<modDef>")) {
    modLoc = modLoc.parent;
  }
  
  return modLoc;
}

loc addModuleToBase(loc base, Module m) = base + modToPath(m.\module.name);

void makeDirRecursively(loc dir) {
  if (!exists(dir.parent)) {
    makeDirRecursively(dir.parent);
  } 
  if (!exists(dir)) {
    mkDirectory(dir);
  }
}

Maybe[loc] lookupFile(QualifiedName name, str ext, list[loc] paths) {
  for (s <- paths) {
    Maybe[loc] resolved = lookupFile(name, ext, s);
    if (just(_) := resolved) {
      return resolved;
    }
  }
  
  return nothing();
}

Maybe[loc] lookupFile(QualifiedName name, str ext, loc path) {
  result = (path + replaceAll("<name>", "::", "/"))[extension = ext];
  if (exists(result)) {
    return just(result);
  }
  
  return nothing();
}

private str modToPath(QualifiedName modul) = replaceAll("<modul>", "::", "/");