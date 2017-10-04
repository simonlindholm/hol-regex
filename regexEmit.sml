structure regexEmit :> regexEmit =
struct

(* intactive use:
  app load ["EmitML", "basis_emitTheory"]
  etc.
*)

val _ = use "HolKernel";
open HolKernel Parse EmitML regexTheory listTheory basis_emitTheory;
(* or listML instead of basis_emitTheory? *)

(* load "regexTheory"; *)

(* open EmitML regexTheory listTheory basis_emitTheory; *)

(*
fun main () =
   let
      val prog = load_programs (CommandLine.arguments())
      val _ = print "Enter architecture, initial register values and default\
                    \ memory content.\n(Enter values as Hex.)\n\
                    \For example: arch = ARMv7-A, pc = A00, r0 = AF, r_ = 10,\n\
                    \             cpsr = 80000010, _psr = 10, mem_ = 0\n> "
      val options = valOf (TextIO.inputLine TextIO.stdIn)
      val trace = input_number (fn i => 0 <= i andalso i <= 5)
                    "Enter trace level [0 - 5]: "
      val count = input_number (fn i => ~1 <= i) "Enter number of cycles: "
   in
      case time (arm_run (int_to_trace trace) prog options) count
      of out as (_, SOME _) => print_arm_run prog out
       | (e, NONE) => out [e]
   end
*)

val _ =
  emitML "" ("regex",
    OPEN ["list"] ::
    MLSIG "type list = listML.list" ::
    ABSDATATYPE (["'a"], `Reg = Eps`) :: 
    (* ABSDATATYPE (["'a"], `Reg = Eps | Sym 'a | Alt Reg Reg | Seq Reg Reg | * Rep Reg`) :: *)
    map DEFN_NOSIG [
      split_def,
      add_to_head_def,
      parts_def
    ] @
    map DEFN [
      accept_def
    ]);

end
