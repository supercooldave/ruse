Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import LabelledOperationalSemantics.
Require Import OperationalSemantics.
Require Import TraceSemantics.
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

Lemma call_address : forall (p p' : Address),
  write_allowed p p' ->
  (protected p /\ data_segment p') \/
  (unprotected p /\ unprotected p') \/
  (protected p /\ unprotected p').
Proof.
Admitted.



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


Theorem fully_abstract_labelled_operational_semantics : 
  forall s1 s2 : State,
    ((s1 ---> s2 -> exists l : Label, s1 ~~ l ~> s2) /\ (forall (l : Label), s1 ~~ l ~> s2 -> s1 ---> s2)).
Proof.
intros.
split.
apply original_semantics_implies_labelled.
apply labelled_semantics_implies_original.
Qed.











(*==============================================
   Theorems  on the trace semantics
==============================================*)

(* TODO : requires interface preservation lemma *)
Lemma trace_semantics_soundness :
  forall p1 p2: MemSec, trace_equivalence p1 p2 -> contextual_equivalence p1 p2.
Proof.
Admitted.

(* TODO *)
Lemma trace_semantics_completeness :
  forall p1 p2: MemSec, contextual_equivalence p1 p2 -> trace_equivalence p1 p2.
Proof.
Admitted.

Theorem fully_abstract_trace_semantics : 
  forall p1 p2 : MemSec, contextual_equivalence p1 p2 <-> trace_equivalence p1 p2.
Proof.
intros.
split.
apply trace_semantics_completeness.
apply trace_semantics_soundness.
Qed.







(*==============================================
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)
Open Scope type_scope.

(* TODO: these should be formalised in terms of lists of labels,
   not just a single label. *)


(* Coq problem: it loses the connection between a state in the ~~ l ~> reduction and its corresponding ~~> assumption *)


Theorem single_trace_implies_label_init : 
  forall (l : Label) (c : MemSec) (ts: TraceState) ,
     (initial_trace c) -- l --> ts -> 
     exists ctx : MemExt, exists st : State,
       (initial c ctx) ~~ l ~> st.
Proof.
Admitted.


Theorem single_trace_implies_label_general : 
  forall (l : Label) (c : MemSec) (p : Address) (r : RegisterFile) (f : Flags) (ts : TraceState),
     Sta (p, r, f, c) -- l --> ts -> 
     exists ctx : MemExt, exists st : State,
       (p, r, f, (plug ctx c)) ~~ l ~> st.
Proof.
Admitted.



Theorem single_label_implies_trace_init : 
  forall (ctx : MemExt) (st : State) (l : Label) (c : MemSec),
    (initial c ctx) ~~ l ~> st -> 
    exists ts: TraceState,
      (initial_trace c) -- l --> ts.
Proof.
Admitted.


Theorem single_label_implies_trace_general : 
  forall (ctx : MemExt) (st : State) (l : Label) (c : MemSec) (p : Address) (r : RegisterFile) (f : Flags),
    (p, r, f, plug ctx c) ~~ l ~> st -> 
    exists ts: TraceState,
      Sta (p, r, f, c) -- l --> ts.
Proof.
Admitted.
