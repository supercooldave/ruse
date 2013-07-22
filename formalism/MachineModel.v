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
Axiom non_overflow_entry_points : no_entrypoints * entrypoint_size < code_size .


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
| write_unprotected : forall (p a : Address), ~ p = 0 -> unprotected a -> write_allowed p a.

Definition entry_jump (p p' : Address) := unprotected p /\ entrypoint p'.
Definition exit_jump (p p' : Address) := protected p /\ unprotected p'.
Definition int_jump (p p' : Address) := protected p /\ protected p' /\ ~ data_segment p'.
Definition ext_jump (p p' : Address) := unprotected p /\ unprotected p'.
Definition same_jump (p p' : Address) := int_jump p p' \/ ext_jump p p'.
Definition valid_jump (p p' : Address) := same_jump p p' \/ entry_jump p p'  \/ exit_jump p p'.


(* Pointers used to set up two stacks*)
Definition SPsec := starting_address  + code_size.
Definition SPext := last_address.

Definition address_returnback_entry_point : Address := starting_address + no_entrypoints * entrypoint_size.


(* =========
Functions that model the switching of the stack
==========*)
Inductive set_stack : Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
| stack_out_to_in : 
  forall (p p' : Address) (m m': Memory) (r r': RegisterFile),
    entry_jump p p' -> 
    unprotected (r SP) -> 
    m' = update m SPext (r SP) -> 
    r' = updateR r SP (lookup m SPsec) -> 
    protected (r' SP) ->
    set_stack p r m p' r' m'
| stack_in_to_out : 
  forall (p p' : Address) (m m' : Memory) (r r': RegisterFile),
    protected (r SP) ->
    exit_jump p p' -> 
    m' = update m SPsec (r SP) -> 
    r' = updateR r SP (lookup m SPext) ->
    unprotected (r' SP) ->
    set_stack p r m p' r' m'
| stack_no_change_i : 
  forall (p p' : Address) (m : Memory) (r : RegisterFile),
    int_jump p p' ->
    protected (r SP) ->
    set_stack p r m p' r m
| stack_no_change_e :
  forall (p p' : Address) (m : Memory) (r : RegisterFile),
    ext_jump p p' ->
    unprotected (r SP) ->
    set_stack p r m p' r m.








(* =========
 Definition of program, component, types of memories and related operations, and states
==========*)
Definition MemSec := { m : Memory | forall (a : Address), domain m a <-> protected a }.
Definition MemExt := { m : Memory | forall (a : Address), domain m a <-> ( a = 0  \/ unprotected a) }.

Parameter domainMS : MemSec -> Address -> Prop.
Parameter domainME : MemExt -> Address -> Prop.
Parameter lookupMS : MemSec -> Address -> Value.
Parameter lookupME : MemExt -> Address -> Value.
Parameter updateMS : MemSec -> Address -> Value -> MemSec.
Parameter updateME : MemExt -> Address -> Value -> MemExt.


Definition compatible := fun (p : MemSec) (c : MemExt) =>
  forall (a : Address), ( (domainMS p a) <-> (~ domainME c a) /\ (domainME c a) <-> (~ domainMS p a)).

Parameter split : Memory -> MemExt * MemSec.
Parameter plug : MemExt -> MemSec -> Memory.

Axiom split_plug_mem : forall (m : Memory) (msec : MemSec) (mext : MemExt), 
  split m = (mext, msec) <-> plug mext msec = m.



(* Complete program state *)
Open Scope type_scope.
Definition StateF (X : Type) := Address * RegisterFile * Flags * X.

Definition State := StateF Memory.
Definition StateSec := StateF MemSec.
Definition StateExt := StateF MemExt.

(* State for the trace semantics *)
Inductive TraceState := 
| Sta : StateSec -> TraceState
| Unk : MemSec -> TraceState. 


Definition getSecMem : Memory -> MemSec :=
  fun (m : Memory) => snd (split m).
Definition getExtMem : Memory -> MemExt :=
  fun (m : Memory) => fst (split m).


Definition p_0 : Address := (S last_address). 
Definition r_0 : RegisterFile :=   fun r : Register => 0.
Definition f_0 : Flags :=   fun f : Flag => false.


Definition initial : MemSec -> MemExt -> State  :=   fun (p : MemSec) (c : MemExt) => ( p_0, r_0, f_0, (plug c p) ).
Definition initial_trace : MemSec -> TraceState  :=   fun (p : MemSec) => (Unk p ).





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


Lemma write_out_address : forall (p p' : Address),
  write_allowed p p' ->
  (protected p /\ data_segment p') \/
  (unprotected p /\ unprotected p') \/
  (protected p /\ unprotected p').
Proof.
intros.
destruct H.
  left. split; auto.
  right. assert (protected p \/ unprotected p). 
     assert (p = 0 \/ protected p \/ unprotected p) by apply (protected_unprotected_coverage p). intuition. intuition.
Qed.


Open Scope nat.

Lemma two_add : forall a b c d, a < b -> c < d -> a + c < b + d.
Proof.
  intros.
  omega.
Qed.


Lemma two_steps : forall a b m, a < b -> a * m < b * m -> a * (S m) < b * (S m).
Proof.
  intros.
  assert (a * m + a < b * m + b) by (apply two_add; auto). 
  assert (a * m + a = a * S m) by auto.
  assert (b * m + b = b * S m) by auto.
  rewrite <- H2. 
  rewrite <- H3.
  auto.
Qed.


Lemma mono_mul : forall (a b c : nat), a < b -> c > 0 -> a * c < b * c.
Proof. 
  intros.
  induction H0. omega.
  apply two_steps; auto.
Qed.


Lemma entrypoint_is_protected :
  forall (p : Address),
    entrypoint p -> protected p.
Proof.
  intros p H. 
  red. 
  red in H. destruct H. destruct H.
  subst.
  split. 
    assert (entrypoint_size > 0) by apply non_zero_entrypoint_size.

    assert (forall (a b : nat), a <= a + b) by (intros; omega).
    apply H1.
      
  unfold last_address.
  assert (no_entrypoints * entrypoint_size < code_size) by apply non_overflow_entry_points.

  assert (x * entrypoint_size < code_size + data_size).
  assert (entrypoint_size > 0) by apply non_zero_entrypoint_size.
  assert (x * entrypoint_size <  no_entrypoints * entrypoint_size).
  apply mono_mul; auto.
  
   omega.

  (* new subgoal *)
  assert (forall (a b c : nat), b < c -> a + b < a + c ) as HP by (intros; omega).
  apply HP with (a := starting_address) in H1.
  omega.
Qed.






(* group azxioms somewhere *)

Axiom correspond_lookups_protected_val :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    protected p ->
    ((lookupMS c p) = (lookup (plug ctx c) p)).
Axiom correspond_lookups_unprotected :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    ( (lookupME ctx p) = (lookup (plug ctx c) p)).
Axiom any_unprotected_correspond_lookups :
  forall (p : Address) (c : MemSec) (ctx ctx' : MemExt),
    protected p ->
    ((lookup (plug ctx' c) p) = (lookup (plug ctx c) p)).
Axiom any_protected_correspond_lookups :
  forall (p : Address) (c c': MemSec) (ctx : MemExt),
    unprotected p ->
    ( (lookup (plug ctx c') p) = (lookup (plug ctx c) p)).

Axiom plug_same_memory :
  forall (ctx me : MemExt) (m c : MemSec),
    plug ctx c = plug me m ->
    ( c = m /\ ctx = me).


Parameter get_trace_state : State -> TraceState.



