Require Import Omega.
Require Import List.


(*==============================================
   This models the memory and all its variants. 
   Instructions are modelled elsewhere (for now).
==============================================*)

(* TODO: Find better home for these -- better still, see if they are in Coq lib. *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  if andb (ble_nat n m) (negb (beq_nat n m)) then true else false.

Definition Address := nat.
Definition Value := nat.



(* Elements that constitute a program and its state *)
(* TODO: change to something else instead of Parameter?*)
Parameter Memory : Set.
Parameter lookup : Memory -> Address -> Value.
Parameter update : Memory -> Address -> Value -> Memory.
Parameter domain : Memory -> Address -> Prop.


(* Axioms from "Tensors of Comodels and Models for Operational Semantics"    by Gordon Plotkin and John Power, MFPS 2008 *)

Axiom mem_lookup_update : forall (m : Memory) (a : Address) (v : Value), 
  lookup (update m a v) a = v.

Axiom mem_update_lookup : forall (m : Memory) (a : Address) (v : Value), 
  update m a (lookup m a) = m.

Axiom mem_update_update_same : forall (m : Memory) (a : Address) (v v' : Value), 
  update (update m a v) a v' = update m a v'.

Axiom mem_update_update_diff : forall (m : Memory) (a a' : Address) (v v' : Value),
  a <> a' -> update (update m a v) a' v' = update (update m a' v') a v.


(* =========
   Memory descriptor and related primitives 
==========*)
Record MemoryDescriptor := MemDesc {
  starting_address_ : nat;
  code_size_ : nat;
  data_size_ : nat;
  no_entrypoints_ : nat
}.

Parameter s : MemoryDescriptor.

Definition starting_address := starting_address_ s.
Definition code_size := code_size_ s.
Definition data_size := data_size_ s.
Definition no_entrypoints := no_entrypoints_ s.

Definition last_address : Address := starting_address + code_size + data_size.

Axiom non_zero_starting_address : starting_address > 0.


(* Memory partitions enforced by the memory descriptor *)
Definition protected (p : Address) : Prop := starting_address <= p /\ p < last_address. 
Definition unprotected (p : Address) : Prop :=
  (p > 0 /\ p < starting_address) \/ last_address <= p.

Parameter entrypoint_size : nat.
Axiom non_zero_entrypoint_size : entrypoint_size > 0.



(*==========
 Auxiliary functions modelling the access control policy 
==========*)
Definition entrypoint (p : Address) : Prop :=
  exists m : nat, m < no_entrypoints /\ p = starting_address + m * entrypoint_size.
Definition data_segment (p : Address) : Prop :=
  starting_address + code_size <= p /\ p < last_address.
Definition return_entrypoint (p : Address) : Prop :=
  p = starting_address + no_entrypoints * entrypoint_size.

Inductive read_allowed : Address -> Address -> Prop :=
  read_protected : forall (p a : Address), protected p -> protected a -> read_allowed p a
| read_unprotected : forall (p a : Address), unprotected p -> unprotected a -> read_allowed p a.
Inductive write_allowed : Address -> Address -> Prop :=
  write_protected : forall (p a : Address), protected p -> data_segment a -> write_allowed p a
| write_unprotected : forall (p a : Address), unprotected a -> write_allowed p a.

Definition entry_jump (p p' : Address) := unprotected p /\ entrypoint p'.
Definition exit_jump (p p' : Address) := protected p /\ unprotected p'.
Definition int_jump (p p' : Address) := protected p /\ protected p' /\ ~ data_segment p'.
Definition ext_jump (p p' : Address) := unprotected p /\ unprotected p'.
Definition same_jump (p p' : Address) := int_jump p p' \/ ext_jump p p'.
Definition valid_jump (p p' : Address) := same_jump p p' \/ entry_jump p p'  \/ exit_jump p p'.


(* Pointers used to set up two stacks*)
Definition SPsec := starting_address  + code_size.
Definition SPext := last_address.

(* =========
Functions that model the switching of the stack
==========*)
Inductive set_stack : MemoryDescriptor -> Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (s : MemoryDescriptor) (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump s p p' -> m' = store m (SPext s) (r SP) -> r' = updateR r SP (lookup m (SPsec s)) -> set_stack s p r m p' r' m'
| stack_in_to_out : forall (s : MemoryDescriptor) (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump s p p' -> m' = store m (SPsec s) (r SP) -> r' = updateR r SP (lookup m (SPext s)) -> set_stack s p r m p' r' m'
| stack_no_change : forall (s : MemoryDescriptor) (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump s p p' -> set_stack s p r m p' r m.





(* =========
   Registers and so forth 
==========*)
Inductive Register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | SP.
Inductive Flag := SF | ZF.
Definition Bit := bool. 

(* Registers *)
Definition RegisterFile := Register -> Value.
(*Definition updateR (r : RegisterFile) (reg : Register) (v : Value) : RegisterFile :=
  fun (reg' : Register) => if (reg = reg') then v else r reg.*)
Parameter updateR : RegisterFile -> Register -> Value -> RegisterFile.

(* Flags *)
Definition Flags := Flag -> Bit. 
Parameter updateF : Flags -> Flag -> Bit -> Flags.







(* =========
 Definition of program, component, types of memories and related operations, and states
==========*)
Definition MemSec := { m : Memory | forall (a : Address), domain m a <-> protected a }.
Definition MemExt := { m : Memory | forall (a : Address), domain m a <-> ( a = 0  \/ unprotected a) }.

Parameter domainMS : MemSec -> Address -> Prop.
Parameter domainME : MemExt -> Address -> Prop.

Definition Program := Memory.
Definition Context := MemExt.

Definition compatible := fun (p : Program) (c : Context) =>
  forall (a : Address), ( (domain p a) <-> (~ domainME c a) /\ (domainME c a) <-> (~ domain p a)).

Parameter split : Memory -> MemExt * MemSec.
Parameter plug : MemExt -> MemSec -> Memory.

Axiom split_plug_mem : forall (m : Memory) (msec : MemSec) (mext : MemExt), 
  split m = (mext, msec) <-> plug mext msec = m.



(* Complete program state *)
Open Scope type_scope.
Definition StateF (X : Type) := Address * RegisterFile * Flags * X.

Definition State := StateF Memory.
Definition StateSec := StateF MemSec.

Close Scope type_scope.

Definition p_0 : Address := (S last_address). 
Definition r_0 : RegisterFile :=   fun r : Register => 0.
Definition f_0 : Flags :=   fun f : Flag => false.

Definition initial : Program -> State  :=   fun p : Program => ( p_0, r_0, f_0, p ).

(* A state is stuck if its pc is in 0 or if it cannot fetch at instruction *)
Definition stuck_state ( p: Address ) ( m : Memory ) :=  
  p < 1 \/ forall i:Instruction, ~ inst (lookup m p) (i) .



(* State for the trace semantics *)
Inductive TraceState := 
| Sta : StateSec -> TraceState
| Unk : MemSec -> TraceState. 




(* =========
   Labels for the trace semantics and the labelled operational
==========*)
Inductive Label := 
| Tau : Label
| Tick : Label
| Write_out : Address -> Value -> Label
| Call : RegisterFile -> Flags -> Value -> Label
| Callback : RegisterFile -> Flags -> Value -> Label
| Return : RegisterFile -> Flags -> Label
| Returnback : RegisterFile -> Flags -> Label.










(*==============================================
   Properties 
    of the protection mechanism 
==============================================*)

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







