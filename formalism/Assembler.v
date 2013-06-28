Require Import Omega.
Require Import List.

Require Import MachineModel.

(*==============================================
   Syntax
==============================================*)

(* Instructions of the low-level language *)
Inductive Instruction :=
 | movl : Register -> Register -> Instruction
 | movs : Register -> Register -> Instruction
 | movi : Register -> Value    -> Instruction
 | add_ : Register -> Register -> Instruction
 | sub_ : Register -> Register -> Instruction
 | cmp  : Register -> Register -> Instruction
 | jmp  : Register             -> Instruction
 | je   : Register             -> Instruction
 | jl   : Register             -> Instruction
 | call : Register             -> Instruction
 | ret  :                         Instruction
 | halt :                         Instruction.



Parameter inst : Value -> Instruction -> Prop.

(*Some axiom stating that each decoded value is unique. *)
Axiom inst_unique_encode : forall (v : Value) (i i' : Instruction), inst v i -> inst v i' -> i = i'.
Axiom inst_unique_decode : forall (v v' : Value) (i : Instruction), inst v i -> inst v' i -> v = v'.
Axiom inst_no_zero : ~ exists i : Instruction, inst 0 i.






(* A state is stuck if its pc is in 0 or if it cannot fetch at instruction *)
Definition stuck_state ( p: Address ) ( m : Memory ) :=  
  p < 1 \/ forall i:Instruction, ~ inst (lookup m p) (i) .








