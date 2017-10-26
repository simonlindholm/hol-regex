PolyML.print_depth 0;

app load ["EmitML", "regexTheory", "basis_emitTheory"];

open HolKernel Parse boolLib proofManagerLib bossLib;

open EmitML regexTheory listTheory basis_emitTheory;

val output_path = "ML/";

emitML output_path ("regex",
  OPEN ["list"] ::
  (* emitML tries to convert CONS into ::, but seems to fail when it's partially
   * applied (?). Declare it manually. *)
  MLSTRUCT "fun CONS a b = a :: b" ::
  DATATYPE (`Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | Rep Reg`) ::
  DATATYPE (`MReg = MEps | MSym bool 'a | MAlt MReg MReg | MSeq MReg MReg
                  | MRep MReg | MInit bool MReg`) ::
  DATATYPE (`CMReg = CMEps | CMSym bool 'a | CMAlt bool bool CMReg CMReg
                   | CMSeq bool bool CMReg CMReg | CMRep bool CMReg
                   | CMInit bool bool bool CMReg`) ::
  map DEFN_NOSIG [
    (* accept *)
    split_def,
    add_to_head_def,
    parts_def,

    (* accept2 *)
    empty_def,
    final_def,
    shift_def,
    acceptM_def,
    mark_reg_def,

    (* accept3 *)
    cempty_def,
    cfinal_def,
    cupdate_def,
    cshift_def,
    acceptCM_def,
    cache_reg_def
  ] @
  map DEFN [
    accept_def,
    accept2_def,
    accept3_def
  ]);
