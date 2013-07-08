Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import Labels.

(* Temporary home for these *)

(*==============================================
   Theorems  on the labelled operational semantics
==============================================*)


Lemma labelled_semantics_implies_original :
  forall (s1 s2 : State) (l : Label),
    s1 ~~ l ~~> s2 ->
    s1 ---> s2.
Proof.
intros s1 s2 l H. 
(* 5 cases for labels *)
inversion H. 
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m') (p' := p') ; auto.  
apply eval_callback with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. 
apply eval_retback with (r' := r') (r'' := r'') (m' := m') (p' := p'); auto. 
apply eval_writeout with (rs := rs) (rd := rd); auto.
(* case of Tau of internal jumps*)
inversion H0; apply eval_int with (p' := p') (r' := r') (f' := f'); subst; apply H0.
 (* case of Tau of external jumps*)
inversion H0; apply eval_ext with (p' := p') (r' := r') (f' := f'); subst; apply H0.
(* case of Tick of internal jumps*)
inversion H0; try (apply eval_int with (p' := p') (r' := r') (f' := f'); subst; apply H0; fail).  
(* case of Tick of external jumps*)
inversion H0; try (apply eval_ext with (p' := p') (r' := r') (f' := f'); subst; apply H0; fail).  
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
    exists l : Label, s1 ~~ l ~~> s2.
Proof.
intros.
inversion H. (* 5 labels *)
exists (x := Call r'' f p'). apply los_eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto.
exists (x := Return r'' f p'). apply los_eval_ret with (r' := r'); auto. 
exists (x := Callback r'' f p'). apply los_eval_callback with (r' := r') (r'' := r'') (m' := m')  (rd := rd); auto.
exists (x := Returnback r'' f p'). apply los_eval_retback with (r' := r'); auto.
exists (x := Write_out (r rd) (r rs)). apply los_eval_writeout; auto. 
 (* cases of internal jumps *)
inversion H0. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tick). admit. 
 (* cases of external jumps *)
inversion H0.
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tau). admit. 
exists (x := Tick). admit. 
Qed.









(*

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
    exists (x := Call r'' f p'). 
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
exists (x := Returnback r'' f p'). apply los_eval_retback with (r' := r'); auto.
*)

