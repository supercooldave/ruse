Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import TraceSemantics.
Require Import OperationalSemantics.
Require Import SameJumpTransitions.
Require Import LabelledOperationalSemantics.
Require Import Labels.

(* Temporary home for these *)



(*==============================================
   Theorems  on the trace semantics
==============================================*)






(*==============================================
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)
Open Scope type_scope.

(* TODO: these should be formalised in terms of lists of labels, not just a single label. *)


Axiom correspond_lookups_protected_val :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    protected p ->
    ((lookupMS c p) = (lookup (plug ctx c) p)).
Axiom correspond_lookups_punrotected :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    ( (lookupME ctx p) = (lookup (plug ctx c) p)).

Axiom correspond_register_lookups_protected :
  forall (p : Address) (r : RegisterFile) (rd : Register) (c : MemSec) (ctx : MemExt) (v : Value),
    protected p ->
    (updateR r rd (lookupMS c v) = updateR r rd (lookup (plug ctx c) v)).
Axiom correspond_register_lookups_unprotected :
  forall (p : Address) (r : RegisterFile) (rd : Register) (c : MemSec) (ctx : MemExt) (v : Value),
    unprotected p ->
    (updateR r rd (lookupME ctx v) = updateR r rd (lookup (plug ctx c) v)).


Parameter get_trace_state : State -> TraceState.


Axiom update_protected : 
  forall (a : Address) (ctx : MemExt) (c :MemSec) (v : Value) (m : Memory),
    data_segment a -> 
    m = update (plug ctx c) (a) (v)-> 
    getSecMem m = updateMS c a v.

Axiom protected_pc_protected_sp : forall (a : Address) (r : RegisterFile),
  protected a ->
  protected (r SP).

Axiom unknown_taus : 
  forall (c : MemSec),
    Unk c -- Tau --> Unk c.

Axiom unknown_ticks : 
  forall (c : MemSec),
    Unk c -- Tick --> Unk c.



Axiom plug_same_memory :
  forall (ctx me : MemExt) (m c : MemSec),
    plug ctx c = plug me m ->
    ( c = m /\ ctx = me).


Theorem single_label_in_labelled_implies_same_label_in_trace : 
  forall (p : Address) (r : RegisterFile) (f : Flags) (ctx : MemExt) (c : MemSec) (l : Label) (st : State) ,
    (p, r, f, plug ctx c) ~~ l ~~> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) -- l --> ts) \/ (Unk c) -- l --> ts).
Proof.
intros p r f ctx c l st H. 
inversion H.
(* one action*)
  (*case Call*) 
  exists (x := Sta (p', r'', f, c)). apply or_intror.  apply tr_call. destruct H6; auto.    
  (*case Return*)
  exists (x := Unk c). apply or_introl. destruct H8.
   rewrite <- (correspond_lookups_protected_val p c ctx H8) in H4. apply tr_return with (sp := SP) ; auto. 
   assert (protected (r SP)). apply protected_pc_protected_sp with (a := p); auto.
   rewrite (correspond_lookups_protected_val (r SP) c ctx H12); auto. apply conj. apply H8. apply H11.
  (*case Callback*)
  exists (x := Unk (updateMS c (r' SP) (S p))). apply or_introl. destruct H6.
   rewrite <- (correspond_lookups_protected_val p c ctx H6) in H4. 
   apply tr_callback with (r' := r') (rd := rd); auto. apply conj; auto.
  (*case Returnback*)
  exists (x := Sta (p', r'', f, c)). apply or_intror. apply tr_returnback. apply H6.
  (*case Writeout*)
  exists (x := Sta ((S p), r, f, c)). apply or_introl. apply tr_writeout ; auto. inversion H5.
   inversion H7. rewrite (correspond_lookups_protected_val p c ctx H11). apply H4.
(* Taus *)
inversion H6 as [ h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14].
  (*case analysis on all possible Taus*)
    (*movl*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p),r', f0, c)). apply or_introl. apply tr_intern. inversion H20. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H21. apply H7. 
    (*movs write in prot*) 
    
      admit.
    (*movi*)
      admit.
    (*cmp*)
      admit.
    (*add*)
      admit.
    (*sub*)
      admit.
    (*call same jump*)
      admit.
    (*ret same jump*)
      admit.
    (*je true*)
      admit.
    (*je false*)
      admit.
    (*jl true*)
      admit.
    (*jl false*)
      admit.
    (*jmp*)
      admit.
    (*halt*)
      exists (x := Sta (0, r, f, c)).  apply or_introl. subst. contradiction. 
(* Taus  external*) 
  exists (x := Unk c). apply or_intror. apply unknown_taus.
(* Tick internal*) 
  exists (x := Sta (0, r, f, c)). apply or_introl. apply tr_internal_tick. 
    apply eval_sec_halt; assert (c = m). apply (plug_same_memory ctx me m c); rewrite H4; reflexivity. rewrite H8. apply H7. 
    assert (c = m). apply (plug_same_memory ctx me m c); rewrite H4; reflexivity. rewrite H8. apply H7.
(* Tick external*)
  exists (x := Unk c). apply or_intror. apply unknown_ticks.
Qed.























