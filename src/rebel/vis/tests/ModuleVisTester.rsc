module rebel::vis::tests::ModuleVisTester

import rebel::vis::ModuleVis;

import salix::App;

App[Model] showVis(loc rebelMod) = createStateMachineVis(rebelMod);