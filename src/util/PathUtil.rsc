module util::PathUtil

import String;
import IO;

import lang::Syntax;

data PathConfig = pathConfig(list[loc] srcs = [], list[loc] libs = []);

loc project(loc file) {
   assert file.scheme == "project";
   return |project://<file.authority>|;
}

PathConfig pathConfig(loc file, list[str] relRoots) {
   assert file.scheme == "project";

   p = project(file);      
 
   return pathConfig(srcs = [ p + r | r <- relRoots]);
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

private str modToPath(QualifiedName modul) = replaceAll("<modul>", "::", "/");