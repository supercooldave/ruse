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


Lemma no_halt_sec : 
  forall (m : MemSec) (p : Address) (i : Instruction),
    i <> halt ->
    inst (lookupMS m p) i->
    (~ inst (lookupMS m p) halt).
Proof.
intros m p i Div In.
red. intros Fl. assert (i = halt). apply (inst_unique_encode (lookupMS m p) i halt In Fl). contradiction.
Qed.

Lemma no_halt_ext : 
  forall (m : MemExt) (p : Address) (i : Instruction),
    i <> halt ->
    inst (lookupME m p) i->
    ~ inst (lookupME m p) halt.
Proof.
intros m p i Div In.
red. intros Fl. assert (i = halt). apply (inst_unique_encode (lookupME m p) i halt In Fl). contradiction.
Qed.

Lemma no_inst_and_not_inst :
  forall (v : Value) (i : Instruction),
    inst v i -> (~ inst v i) -> False.
Proof.
intros.
unfold not in H0. 
destruct H0.
apply H.
Qed.


(* A state is stuck if its pc is in 0 or if it cannot fetch at instruction *)
Definition stuck_state ( p: Address ) ( m : MemSec ) :=  
  p < 1 \/ forall i:Instruction, ~ inst (lookupMS m p) (i) .








