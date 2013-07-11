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


Ltac grab_2nd_argument H id :=
  match goal with
  | [ H' : _ _ ?X  |- _ ]    => match H with
                                | H' => remember X as id
                                end
  end.

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
inversion H0.
  (*movl*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0.
   grab_2nd_argument H8 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H8. 
  (*movs*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_sec m p j). rewrite Heqj. intro. discriminate. apply H9.
  (*movi*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H6.
  (*cmp*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H6.
  (*add*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H9.
  (*sub*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H9.
  (*call*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_sec m p j). rewrite Heqj. intro. discriminate. apply H9.
  (*ret*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_sec m p j). rewrite Heqj. intro. discriminate. apply H8.
  (*je true*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*je false*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jl true*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jl false*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jmp*)
  exists (x := Tau). apply los_eval_int with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_sec m' p j). rewrite Heqj. intro. discriminate. apply H6.
  (*halt*) 
  exists (x := Tick); apply los_eval_int_halt with (p' := p') (r' := r') (f' := f'). subst; apply H0. apply H4.
 (* cases of external jumps *)
inversion H0.
  (*movl*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0.
   grab_2nd_argument H8 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H8. 
  (*movs*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me p j). rewrite Heqj. intro. discriminate. apply H8.
  (*movi*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H6.
  (*cmp*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H6.
  (*add*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H9.
  (*sub*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H9.
  (*call*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H9 j. apply (no_halt_ext me p j). rewrite Heqj. intro. discriminate. apply H9.
  (*ret*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me p j). rewrite Heqj. intro. discriminate. apply H8.
  (*je true*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*je false*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jl true*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jl false*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H8 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H8.
  (*jmp*)
  exists (x := Tau). apply los_eval_ext with (p' := p') (r' := r') (f' := f'). subst; apply H0. 
   grab_2nd_argument H6 j. apply (no_halt_ext me' p j). rewrite Heqj. intro. discriminate. apply H6.
   (*halt*)
   exists (x := Tick). apply los_eval_ext_halt with (p' := p') (r' := r') (f' := f'). subst. apply H0. apply H4.
Qed.





