PolyML.print_depth 0;

app load ["EmitML", "regexTheory", "basis_emitTheory"];

open HolKernel Parse boolLib proofManagerLib bossLib;

open EmitML regexTheory listTheory basis_emitTheory;

val output_path = "";

emitML output_path ("regex",
  OPEN ["list"] ::
  MLSIG "type list = listML.list" ::
  ABSDATATYPE (["'a"], `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`) ::
  map DEFN_NOSIG [
    split_def,
    add_to_head_def,
    parts_def
  ] @
  map DEFN [
    accept_def
  ]);
