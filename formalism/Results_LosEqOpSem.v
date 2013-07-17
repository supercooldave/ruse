Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import Labels.
Require Import MyTactics. 

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
inversion H0; 
  try (apply eval_int with (p' := S p) (r' := r') (f' := f'); subst; apply H0; fail);
  try(apply eval_int with (p' := p') (r' := r') (f' := f'); subst; apply H0; fail). 
  subst. unfold not in H1. destruct H1; auto.
 (* Case of Tau of external jumps*)
inversion H0; 
  try (apply eval_ext with (p' := S p) (r' := r') (f' := f'); subst; apply H0; fail); 
  try(apply eval_ext with (p' := p') (r' := r') (f' := f'); subst; apply H0; fail). 
  subst. unfold not in H1. destruct H1; auto.
(* case of Tick of internal jumps*)
inversion H0; try (contradiction_diff_inst_halt; fail).
  (*halt*)
  apply eval_int with (p' := 0) (r' := r') (f' := f'). subst; auto.
(* case of Tick of external jumps*)
inversion H0; try (contradiction_diff_inst_halt; fail).
  (*halt*)
  apply eval_ext with (p' := 0) (r' := r') (f' := f'); subst; auto.
Qed.


Lemma original_semantics_implies_labelled :
  forall s1 s2 : State,
    s1 ---> s2 ->
    exists l : Label, s1 ~~ l ~~> s2.
Proof.
intros.
inversion H. (* 5 labels *)
exists (x := Call r'' f p'). apply los_eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto.
exists (x := Return r f p'). apply los_eval_ret with (r' := r'); auto. 
exists (x := Callback r f p'). apply los_eval_callback with (r' := r') (r'' := r'') (m' := m')  (rd := rd); auto.
exists (x := Returnback r'' f p'). apply los_eval_retback with (r' := r'); auto.
exists (x := Write_out (r rd) (r rs)). apply los_eval_writeout; auto. 
 (* cases of internal jumps *)
inversion H0; try(same_domain_step_correspond_semantic).
  (*halt*) 
  exists (x := Tick). apply los_eval_int_halt with (p' := 0) (r' := r') (f' := f'). subst; apply H0. auto. 
 (* cases of external jumps *)
inversion H0; try(same_domain_step_correspond_semantic).
   (*halt*)
   exists (x := Tick). apply los_eval_ext_halt with (p' := 0) (r' := r') (f' := f'). subst. apply H0. auto.
Qed.






