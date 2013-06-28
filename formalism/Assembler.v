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




<<<<<<< HEAD





(*==============================================
   Trace Semantics
==============================================*)

(* TODO:  need to define a ProtectedMemory for the trace state 
   ####### Dave ######*) 
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
  unprotected (r rd) ->
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


(*TODO  change the definition to consider only secure programs, not whole programs like now *)
Definition trace_equivalence : Program -> Program -> Prop :=
  fun p1 p2 : Program => forall p1' p2' : TraceState, forall l1 : list Label, 
    Sta (initial p1) == l1 ==>> p1' <->
    Sta (initial p2) == l1 ==>> p2'.







(*==============================================
   Theorems  on the trace semantics
==============================================*)

(* TODO : requires interface preservation lemma *)
Lemma trace_semantics_soundness :
  forall p1 p2: Program, trace_equivalence p1 p2 -> contextual_equivalence p1 p2.
Proof.
Admitted.

(* TODO *)
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

(* rules for reduction across the same domain (prot - prot) or (unprot - unprot) *)
Reserved Notation "S '~~>' S'" (at level 50, left associativity).

Inductive eval_same_dom : State -> State -> Prop :=
| sd_eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
  inst (lookup m p) (movl rd rs) -> 
  same_jump p (S p) ->
  read_allowed p (r rs) -> 
  r' = updateR r rd (lookup m (r rs)) ->  
    (p, r, f, m) ~~> (S p, r', f, m)
    
| sd_eval_movs_prot : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) -> 
  protected p->
  protected (r rd)->
  m' = update m (r rd) (r rs) ->  
  (p, r, f, m) ~~> (S p, r, f, m')

| sd_eval_movs_unprot : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) -> 
  unprotected p->
  unprotected (r rd)->
  m' = update m (r rd) (r rs) ->  
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


(* rules for reduction that cross a domain, effectively creating a label *)
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

| los_eval_writeout : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) ->
  protected p->
  unprotected (r rd)->
  m' = update m (r rd) (r rs) ->  
  (p, r, f, m) ~~ Write_out (r rd) (r rs) ~> (S p, r, f, m')

  where "S '~~' L '~>' S'" := (eval_trace S L S') : type_scope.



(*==============================================
   Theorems  on the labelled operational semantics
==============================================*)


Lemma labelles_semantics_implies_original :
  forall (s1 s2 : State) (l : Label),
    s1 ~~ l ~> s2 ->
    s1 ---> s2.
Proof.
intros.
destruct H. destruct H; auto. 
apply eval_movl with (rs := rs) (rd := rd); auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
apply eval_movi with (i := i) (rd := rd); auto.
apply eval_compare  with (r1 := r1) (r2 := r2); auto.
apply eval_add with (rs := rs) (rd := rd) (v := v); auto.
apply eval_sub with (rs := rs) (rd := rd) (v := v); auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_introl ; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_introl; auto.
apply eval_je_true with (ri := ri); auto.
apply eval_je_false with (ri := ri); auto.
apply eval_jl_true with (ri := ri); auto.
apply eval_jl_false with (ri := ri); auto.
apply eval_jump with (rd := rd); auto.
apply eval_halt; auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_intror. apply or_introl; auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_intror. apply or_intror; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_intror. apply or_intror; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_intror; auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
Qed.



(* TODO: besides the problem with the admits, i don't know how to call the other labels into place
 there should be  5 more cases generated for them (writeout, call callback return returnback) *)
Lemma original_semantics_implies_labelled :
  forall s1 s2 : State,
    s1 ---> s2 ->
    exists l : Label, s1 ~~ l ~> s2.
Proof.
intros.
destruct H. 
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movl with (rs := rs) (rd := rd); auto.
admit.
(* intuitively:

destruct H1. apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movs_prot with (rd := rd) (rs := rs) ; auto.

 big problem. i get an address 'a', and the proof has (r rd), and i don't know how to unify them *)
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movi with (i := i) (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_compare with (r1 := r1) (r2 := r2); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_add with (rs := rs) (rd := rd) (v := v); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_sub with (rs := rs) (rd := rd) (v := v); auto.
admit.
admit.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jump with (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_halt; auto.
Qed.



=======
>>>>>>> 4fd312092aec3e6103109af6803792a6917abb13
