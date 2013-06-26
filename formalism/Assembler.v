Require Import Omega.
Require Import List.


(*==============================================
   Syntax
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


(* Elements that constitute a program and its state *)
(* TODO: change to something else instead of Parameter?*)
Parameter Memory : Set.
Parameter lookup : Memory -> Address -> Value.
Parameter update : Memory -> Address -> Value -> Memory.
Parameter domain : Memory -> Address -> Prop.


(* Axioms from "Tensors of Comodels and Models for Operational Semantics" 
   by Gordon Plotkin and John Power, MFPS 2008 *)
Axiom mem_lookup_update : forall (m : Memory) (a : Address) (v : Value), 
  lookup (update m a v) a = v.
Axiom mem_update_lookup : forall (m : Memory) (a : Address) (v : Value), 
  update m a (lookup m a) = m.
Axiom mem_update_update_same : forall (m : Memory) (a : Address) (v v' : Value), 
  update (update m a v) a v' = update m a v'.
Axiom mem_update_update_diff : forall (m : Memory) (a a' : Address) (v v' : Value),
  a <> a' -> update (update m a v) a' v' = update (update m a' v') a v.


Definition RegisterFile := Register -> Value.
(*Definition updateR (r : RegisterFile) (reg : Register) (v : Value) : RegisterFile :=
  fun (reg' : Register) => if (reg = reg') then v else r reg.*)
Parameter updateR : RegisterFile -> Register -> Value -> RegisterFile.

Definition Flags := Flag -> Bit. 
Parameter updateF : Flags -> Flag -> Bit -> Flags.


(* Memory descriptor and related primitives *)
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

Parameter entrypoint_size : nat.
Axiom non_zero_entrypoint_size : entrypoint_size > 0.






(* Auxiliary functions modelling the access control policy *)
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

(* Auxiliary functions that model the switching between stacks *)
Inductive set_stack : Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump p p' -> m' = update m SPext (r SP) -> r' = updateR r SP (lookup m SPsec) -> set_stack p r m p' r' m'
| stack_in_to_out : forall (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump p p' -> m' = update m SPsec (r SP) -> r' = updateR r SP (lookup m SPext) -> set_stack p r m p' r' m'
| stack_no_change : forall (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump p p' -> set_stack p r m p' r m.








(*==============================================
   Operational Semantics
==============================================*)
Open Scope type_scope.

(* State of the operational semantics *)
Definition State := Address * RegisterFile * Flags * Memory.

Parameter inst : Value -> Instruction -> Prop.

(*Some axiom stating that each decoded value is unique. *)
Axiom inst_unique_encode : forall (v : Value) (i i' : Instruction), inst v i -> inst v i' -> i = i'.
Axiom inst_unique_decode : forall (v v' : Value) (i : Instruction), inst v i -> inst v' i -> v = v'.
Axiom inst_no_zero : ~ exists i : Instruction, inst 0 i.

(* Operational rules *)
Reserved Notation "S '--->' S'" (at level 50, left associativity).

Inductive evalR : State -> State -> Prop :=
| eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
  inst (lookup m p) (movl rd rs) -> 
  same_jump p (S p) ->
  read_allowed p (lookup m (r rs)) -> 
  r' = updateR r rd (lookup m (r rs)) ->  
  (p, r, f, m) ---> (S p, r', f, m)
  
| eval_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (lookup m (r rd)) -> 
  m' = update m (lookup m (r rs)) (r rd) ->  
  (p, r, f, m) ---> (S p, r, f, m')
  
| eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (movi rd i) -> 
  same_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) ---> (S p, r', f, m)
  
| eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : Memory) (r1 r2 : Register),
  inst (lookup m p) (cmp r1 r2) -> 
  same_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) ---> (S p, r, f', m)
  
| eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (add_ rd rs) -> 
  same_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ---> (S p, r', f', m)
  
| eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (sub_ rd rs) -> 
  same_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ---> (S p, r', f', m)
  
| eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = r rd ->
  valid_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  valid_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ---> (p', r'', f, m')
  
| eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (jmp rd) -> 
  p' = r rd ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : Memory),
  inst (lookup m p) halt ->
  (p, r, f, m) ---> (0, r, f, m)
  
  where "S '--->' S'" := (evalR S S') : type_scope.


(* contextual equivalence *)
(* TODO: eliminate Program cause redundancy? *) 
Definition MemSec := { m : Memory | forall (a : Address), domain m a <-> protected a }.
Definition MemExt := { m : Memory | forall (a : Address), domain m a <-> ( a = 0  \/ unprotected a) }.

Parameter domainMS : MemSec -> Address -> Prop.
Parameter domainME : MemExt -> Address -> Prop.

Definition Program := Memory.
Definition Context := MemExt.

Definition compatible := fun (p : Program) (c : Context) =>
  forall (a : Address), ( (domain p a) <-> (~ domainME c a) /\ (domainME c a) <-> (~ domain p a)).

Inductive do_n_steps: State -> nat -> State -> Prop :=
| do_0 : forall sta, do_n_steps sta 0 sta
| do_Sn : forall n sta sta' sta'', 
  sta ---> sta' ->
  do_n_steps sta' n sta'' ->
  do_n_steps sta (S n) sta''.

Definition anysteps (n : nat) (sta  : State) := 
  exists n' : nat , exists sta' : State,
      n' >= n /\ do_n_steps sta n' sta'.

Definition diverge (sta : State) := forall n, anysteps n sta.

Definition p_0 : Address := (S last_address). 
Definition r_0 : RegisterFile :=   fun r : Register => 0.
Definition f_0 : Flags :=   fun f : Flag => false.

Definition initial : Program -> State  :=   fun p : Program => ( p_0, r_0, f_0, p ).

Definition plug : Program -> Context -> Program := fun (p : Program) (c : Context) => 
  p.  (* TODO: wrong, should plug p and c, not return p*)

Definition contextual_equivalence : Program -> Program -> Prop := fun p1 p2 : Program => 
  forall c : Context, compatible p1 c -> compatible p2 c ->
    ( (diverge (initial (plug p1 c))) <-> (diverge (initial (plug p2 c))) ).
  




(*==============================================
   Properties
==============================================*)
(* TODO: a set of small lemmas that prove semi-trivial properties on MemSec, MemExt and so on *)









(*==============================================
   Trace Semantics
==============================================*)

(* TODO:  need to define a ProtectedMemory for the trace state *) 
(* State for the trace semantics *)
Inductive TraceState := 
| Sta : State -> TraceState
| Unk : Memory -> TraceState. 

(* A state is stuck if its pc is in 0 or if it cannot fetch at instruction *)
Definition stuck_state ( p: Address ) ( m : Memory ) :=  
  p < 1 \/ forall i:Instruction, ~ inst (lookup m p) (i) .


(* Labels for the trace semantics*)
Inductive Label := 
| Tau : Label
| Tick : Label
| Write_out : Address -> Value -> Label
| Call : RegisterFile -> Flags -> Value -> Label
| Callback : RegisterFile -> Flags -> Value -> Label
| Return : RegisterFile -> Flags -> Label
| Returnback : RegisterFile -> Flags -> Label.


(* Trace semantics *)
Reserved Notation " T '--' L '-->' T' " (at level 50, left associativity).

Inductive trace : TraceState -> Label -> TraceState -> Prop :=
| tr_intern : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': Memory),
  (p, r, f, m) ---> (p', r', f', m') ->
  int_jump p p' ->
  Sta (p, r, f, m) -- Tau --> Sta (p', r', f', m')

| tr_internal_tick : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': Memory),
  (p, r, f, m) ---> (p', r', f', m') ->
  stuck_state p' m' ->
  Sta (p, r, f, m) -- Tick --> Sta (p', r', f', m')

| tr_writeout : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory) (rd rs : Register),
  int_jump p (S p) ->
  inst (lookup m p ) (movs rd rs)->
  unprotected (lookup m (r rd)) ->
  Sta (p, r, f, m) --  Write_out (r rd) (r rs) --> Sta ( (S p), r, f, m) 

| tr_call : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory),
  entrypoint p ->
  (Unk m) -- Call r f p  --> Sta (p, r, f, m)

| tr_returnback : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory),
  return_entrypoint p ->
  (Unk m) -- Returnback r f  --> Sta (p, r, f, m)

| tr_callback : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory) (rd : Register),
  inst (lookup m p) (call rd) ->
  exit_jump p (lookup m (r rd)) ->
  Sta (p, r, f, m) -- Callback r f (lookup m (r rd)) --> (Unk m)

| tr_return : forall (p p' : Address) (r : RegisterFile) (f: Flags) (m: Memory) (sp : Register),
  p' = lookup m (r sp) ->
  exit_jump p p'->
  inst (lookup m p) (ret) ->
  Sta (p, r, f, m) -- Return r f  --> (Unk m)

where "T '--' L '-->' T'" := (trace T L T') : type_scope.


(* reflexive-transitive closure of the trace semantics *)
Reserved Notation " T '==' L '==>>' T' " (at level 51, left associativity).

Inductive trace_semantics : TraceState -> ( list Label ) -> TraceState -> Prop :=
| trace_refl : forall (t : TraceState),
  t == nil ==>> t

| trace_tau : forall (t t' : TraceState),
  t -- Tau --> t' ->
  t == nil ==>> t'

| trace_trans : forall (t t' t'' : TraceState) (l : Label) (l' : list Label),
  t -- l --> t' ->
  t' == l' ==>> t''->
  t == cons l l' ==>> t''

where "T '==' L '==>>' T'" := (trace_semantics T L T') : type_scope.


Definition trace_equivalence : Program -> Program -> Prop :=
  fun p1 p2 : Program => forall p1' p2' : TraceState, forall l1 : list Label, 
    Sta (initial p1) == l1 ==>> p1' <->
    Sta (initial p2) == l1 ==>> p2'.







(*==============================================
   Theorems 
==============================================*)

Lemma trace_semantics_soundness :
  forall p1 p2: Program, trace_equivalence p1 p2 -> contextual_equivalence p1 p2.
Proof.
Admitted.

Lemma trace_semantics_completeness :
  forall p1 p2: Program, contextual_equivalence p1 p2 -> trace_equivalence p1 p2.
Proof.
Admitted.

Theorem fully_abstract_trace_semantics : 
  forall p1 p2 : Program, contextual_equivalence p1 p2 <-> trace_equivalence p1 p2.
Proof.
intros.
split.
apply trace_semantics_completeness.
apply trace_semantics_soundness.
Qed.








(*==============================================
   Labelled Operational Semantics
==============================================*)

Reserved Notation "S '~~>' S'" (at level 50, left associativity).

Inductive eval_same_dom : State -> State -> Prop :=
| sd_eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
  inst (lookup m p) (movl rd rs) -> 
  same_jump p (S p) ->
  read_allowed p (lookup m (r rs)) -> 
  same_jump p (r rd) ->  (* this read rule is only for readin in the same domain of the pc *)
  r' = updateR r rd (lookup m (r rs)) ->  
    (p, r, f, m) ~~> (S p, r', f, m)
    
| sd_eval_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (lookup m (r rd)) -> 
  same_jump p (r rd)->  (* this write rule is only for writing in the same domain of the pc *)
  m' = update m (lookup m (r rs)) (r rd) ->  
  (p, r, f, m) ~~> (S p, r, f, m')
    
| sd_eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (movi rd i) -> 
  same_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) ~~> (S p, r', f, m)
  
| sd_eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : Memory) (r1 r2 : Register),
  inst (lookup m p) (cmp r1 r2) -> 
  same_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) ~~> (S p, r, f', m)
  
| sd_eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (add_ rd rs) -> 
  same_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ~~> (S p, r', f', m)
  
| sd_eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (sub_ rd rs) -> 
  same_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ~~> (S p, r', f', m)
  
| sd_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = r rd ->
  same_jump p p' ->  (*only jumps between the same domains*)
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  same_jump p p' -> (* only jumps between the same domains*)
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~> (p', r'', f, m')
  
| sd_eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (jmp rd) -> 
  p' = r rd ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : Memory),
  inst (lookup m p) halt ->
  (p, r, f, m) ~~> (0, r, f, m)
  
  where "S '~~>' S'" := (eval_same_dom S S') : type_scope.


Reserved Notation "S '~~' L '~>' S'" (at level 50, left associativity).

Inductive eval_trace : State -> Label -> State -> Prop :=
| los_eval_same : forall (s s' : State),
  s ~~> s'->
  s ~~ Tau ~> s'

| los_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = r rd ->
  entry_jump p p' ->  
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~ Call r f p' ~> (p', r, f, m)

| los_eval_callback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = r rd ->
  exit_jump p p' ->  
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~ Callback r f p' ~> (p', r, f, m)

| los_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  exit_jump p p' -> 
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Return r f ~> (p', r'', f, m')
  
| los_eval_retback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  entry_jump p p' -> 
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Returnback r f ~> (p', r'', f, m')

(*TODO: writeout*)
  
  where "S '~~' L '~>' S'" := (eval_trace S L S') : type_scope.


Lemma original_semantics_implies_labelled :
  forall s1 s2 : State,
    s1 ---> s2 ->
    exists l : Label, s1 ~~ l ~> s2.
Proof.
intros.
destruct H.
Admitted.


Lemma labelles_semantics_implies_original :
  forall (s1 s2 : State) (l : Label),
    s1 ~~ l ~> s2 ->
    s1 ---> s2.
Proof.
intros.
destruct H. destruct H; auto. 
apply eval_movl with (rs := rs) (rd := rd); auto.
apply eval_movs with  (rs := rs) (rd := rd); auto.


Admitted.

(*TODO: generate labelled operational semantics

  from this, generate the trace semantics HOOOW *) 