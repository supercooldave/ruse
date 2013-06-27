Require Import Omega.
Require Import List.
Require Import MachineModel.

(*==============================================
   Syntax
==============================================*)

Inductive Register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | SP.
Inductive Flag := SF | ZF.
Definition Bit := bool. 

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



Definition RegisterFile := Register -> Value.
(*Definition updateR (r : RegisterFile) (reg : Register) (v : Value) : RegisterFile :=
  fun (reg' : Register) => if (reg = reg') then v else r reg.*)
Parameter updateR : RegisterFile -> Register -> Value -> RegisterFile.

Definition Flags := Flag -> Bit. 
Parameter updateF : Flags -> Flag -> Bit -> Flags.


Lemma not_protected_zero : ~ protected 0.
Proof.
  intro.
  unfold protected in H. 
  assert (starting_address > 0) by apply non_zero_starting_address.
  omega.
Qed.

Lemma not_unprotected_zero : ~ unprotected 0.
Proof.
  intro.
  unfold unprotected in H.
  unfold last_address in H.
  assert (starting_address > 0) by (apply non_zero_starting_address).
  destruct H; omega.
Qed.

Lemma protected_unprotected_disjoint :
  forall (p : Address), not (protected p /\ unprotected p).
Proof.
  intros.
  intro.
  unfold protected, unprotected in H.
  destruct H.
  omega.
Qed.

Lemma protected_unprotected_coverage :
  forall (p : Address), p = 0 \/ protected p \/ unprotected p.
Proof.
  intros.
  unfold protected, unprotected.
  unfold Address in *.
  omega.
Qed. 



(* Labels for the trace semantics*)
Inductive Label := 
| Tau : Label
| Tick : Label
| Write_out : Address -> Value -> Label
| Call : RegisterFile -> Flags -> Value -> Label
| Callback : RegisterFile -> Flags -> Value -> Label
| Return : RegisterFile -> Flags -> Label
| Returnback : RegisterFile -> Flags -> Label.



(* Auxiliary functions that model the switching between stacks *)
Inductive set_stack : Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump p p' -> m' = update m SPext (r SP) -> r' = updateR r SP (lookup m SPsec) -> set_stack p r m p' r' m'
| stack_in_to_out : forall (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump p p' -> m' = update m SPsec (r SP) -> r' = updateR r SP (lookup m SPext) -> set_stack p r m p' r' m'
| stack_no_change : forall (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump p p' -> set_stack p r m p' r m.


(*==============================================
   Properties
==============================================*)
(* TODO: a set of small lemmas that prove semi-trivial properties on MemSec, MemExt and so on *)




