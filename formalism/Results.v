Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import TraceSemantics.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import Labels.

(* Temporary home for these *)

(*==============================================
   Theorems  on the labelled operational semantics
==============================================*)


Lemma labelled_semantics_implies_original :
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
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto.
apply eval_je_true with (ri := ri); auto.
apply eval_je_false with (ri := ri); auto.
apply eval_jl_true with (ri := ri); auto.
apply eval_jl_false with (ri := ri); auto.
apply eval_jump with (rd := rd); auto.
apply eval_halt; auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. 
apply eval_call_in_to_out with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. 
apply eval_ret with (r' := r') (r'' := r'') (m' := m') (p' := p') ; auto.  
apply eval_ret_out_to_in with (r' := r') (r'' := r'') (m' := m') (p' := p'); auto. 
apply eval_movs with (rs := rs) (rd := rd); auto.
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


Lemma original_semantics_implies_labelled :
  forall s1 s2 : State,
    s1 ---> s2 ->
    exists l : Label, s1 ~~ l ~> s2.
Proof.
intros.
destruct H. 
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movl with (rs := rs) (rd := rd); auto.
apply write_out_address in H1. destruct H1 as [[H1 H1'] | [[H1 H1'] | [H1 H1']]].
  exists (x := Tau). apply los_eval_same. apply sd_eval_movs_prot with (rs := rs) (rd := rd); auto. 
   apply write_protected; auto.
  exists (x := Tau). apply los_eval_same. apply sd_eval_movs_unprot with (rs := rs) (rd := rd); auto. 
   apply write_unprotected; auto. destruct p; auto. assert (~ unprotected 0) by apply not_unprotected_zero. contradiction.
  exists (x := Write_out (r rd) (r rs)). apply los_eval_writeout; auto. apply write_unprotected; auto. 
   destruct p; auto. assert (~ protected 0) by apply not_protected_zero. contradiction.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movi with (i := i) (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_compare with (r1 := r1) (r2 := r2); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_add with (rs := rs) (rd := rd) (v := v); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_sub with (rs := rs) (rd := rd) (v := v); auto.
destruct H1. 
  destruct H1.
    exists (x := Tau). apply los_eval_same. 
      apply sd_eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_introl ; auto.
    exists (x := Tau). apply los_eval_same.
      apply sd_eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_intror ; auto.
  destruct H1.
    exists (x := Call r f p'). 
      apply los_eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. red. split ; trivial. 
destruct H1. 
  destruct H1.
    exists (x := Tau). apply los_eval_same. 
      apply sd_eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_introl ; auto.
    exists (x := Tau). apply los_eval_same. 
      apply sd_eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_intror ; auto.
    destruct H1.
    exists (x := Return r f p'). apply los_eval_ret with (r' := r'); auto. red. split ; trivial.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jump with (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_halt; auto.
exists (x := Callback r f p'). apply los_eval_callback with (r' := r') (r'' := r'') (m' := m')  (rd := rd); auto.
exists (x := Returnback r f p'). apply los_eval_retback with (r' := r'); auto.
Qed.











(*==============================================
   Theorems  on the trace semantics
==============================================*)






(*==============================================
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)
Open Scope type_scope.

(* TODO: these should be formalised in terms of lists of labels, not just a single label. *)

Axiom correspond_lookups_protected :
  forall (p : Address) (i : Instruction) (c : MemSec) (ctx : MemExt),
    protected p ->
    (inst (lookupMS c p) i <-> inst (lookup (plug ctx c) p) i).
Axiom correspond_lookups_punrotected :
  forall (p : Address) (i : Instruction) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    (inst (lookupME ctx p) i <-> inst (lookup (plug ctx c) p) i).

Axiom correspond_register_lookups_protected :
  forall (p : Address) (r : RegisterFile) (rs rd : Register) (c : MemSec) (ctx : MemExt),
    protected p ->
    (updateR r rd (lookupMS c (r rs)) = updateR r rd (lookup (plug ctx c) (r rs))).
Axiom correspond_register_lookups_unprotected :
  forall (p : Address) (r : RegisterFile) (rs rd : Register) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    (updateR r rd (lookupME ctx (r rs)) = updateR r rd (lookup (plug ctx c) (r rs))).






















(* here is a bunch of FALSE theorems, which are only temporarly Admitted
   and which i use to remember how to do things in Coq in certain cases
   *)



Theorem single_trace_implies_label_general : 
  forall (l : Label) (c : MemSec) (p : Address) (r : RegisterFile) (f : Flags) (ts : TraceState),
     Sta (p, r, f, c) -- l --> ts -> 
     exists ctx : MemExt, exists st : State,
       (p, r, f, (plug ctx c)) ~~ l ~> st.
Proof.
intros.
inversion H. inversion H6.   (* how do i create the ctx?? *)
Admitted.

Theorem single_label_implies_trace_general_FAILED : 
  forall (ctx : MemExt) (st : State) (l : Label) (c : MemSec) (p : Address) (r : RegisterFile) (f : Flags),
    (p, r, f, plug ctx c) ~~ l ~> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) -- l --> ts) \/ (Unk c) -- l --> ts).
Proof.
intros.
inversion H. 
inversion H0. 
  destruct H10.
  exists (x := Sta (S p, r', f, c)). apply or_introl. apply tr_intern. apply sec_eval_movl with (rd := rd) (rs := rs). destruct H10. subst.
   rewrite (correspond_lookups_protected p (movl rd rs) c ctx H10); trivial; auto. auto. auto.
   destruct H10. rewrite (correspond_register_lookups_protected p r rs rd c ctx H10); trivial. auto.
  admit. (* this case cannot be true! there is no Tau for unprotected code in the trace semantics *)
Admitted.


Theorem single_label_implies_trace_general : 
  forall (ctx : MemExt) (st : State) (l : Label) (c : MemSec) (p : Address) (r : RegisterFile) (f : Flags),
    protected p ->
    (p, r, f, plug ctx c) ~~ l ~> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) -- l --> ts)).
Proof.
intros ctx st l c p r f P_prot H. inversion H.
  admit.
  exists (x := Unk c). rewrite <- H7 in H. rewrite <- H8 in H. inversion H. subst. 
Admitted.