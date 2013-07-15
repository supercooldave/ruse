Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import TraceSemantics.
Require Import OperationalSemantics.
Require Import SameJumpTransitions.
Require Import LabelledOperationalSemantics.
Require Import Labels.





(*==============================================
   Lemmas  on the operational semantics
==============================================*)




Ltac asd :=
  match goal with
  | [ H' : int_jump ?X _  |- _ ] => 
    match goal with
      | [H'' : unprotected X |- _ ] =>
        (destruct H' as [Ha Hb]; destruct Hb as [Hb Hc]; assert (not (protected X /\ unprotected X)) as Hn; apply (protected_unprotected_disjoint X); unfold not in Hn; destruct Hn; split; apply Ha; apply H'')
    end
  end.



Lemma unused_mem_sec :
  forall (p1 p2 : Address) (r1 r2 : RegisterFile) (f1 f2 : Flags) (ctx1 ctx2 : MemExt) (c11 c21 : MemSec),
    unprotected p1 ->
    unprotected p2 ->
    (p1,r1,f1, plug ctx1 c11) ---> (p2, r2, f2, plug ctx2 c11) ->
    (p1,r1,f1, plug ctx1 c21) ---> (p2, r2, f2, plug ctx2 c21).
Proof.
intros p1 p2 r1 r2 f1 f2 ct1 ct2 c11 c21 Hp1 Hp2 Tr1.
inversion Tr1.
(*call*)
destruct H9. apply (entrypoint_is_protected) in H13. assert (not (protected p2 /\ unprotected p2)). 
apply (protected_unprotected_disjoint p2). unfold not in H14. destruct H14. split. apply H13. apply Hp2.
(*ret*)
destruct H9. assert (not (protected p1 /\ unprotected p1)). 
apply (protected_unprotected_disjoint p1). unfold not in H13. destruct H13. split. apply H9. apply Hp1.
(*callback*)
destruct H9. assert (not (protected p1 /\ unprotected p1)). 
apply (protected_unprotected_disjoint p1). unfold not in H16. destruct H16. split. apply H9. apply Hp1.
(*retback*)
destruct H10. apply (entrypoint_is_protected) in H13. assert (not (protected p2 /\ unprotected p2)). 
apply (protected_unprotected_disjoint p2). unfold not in H14. destruct H14. split. apply H13. apply Hp2.
(*writeout*)
destruct H8. assert (not (protected p1 /\ unprotected p1)). 
apply (protected_unprotected_disjoint p1). unfold not in H12. destruct H12. split. apply H8. apply Hp1.
(*internal *)  
inversion H0.
  (*movl*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*movs*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*movi*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*cmp*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*add*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*sub*)
  destruct H17 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*call*)
  destruct H18 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*ret*)
  destruct H18 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*je t*)
  destruct H19 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*je f*)
  destruct H19 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*jl t*)
  destruct H19 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*jl f*)
  destruct H19 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*je t*)
  destruct H18 as [Ha Hb]. destruct Hb as [Hb Hc]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split. apply Ha. apply Hp1.
  (*halt*)
  subst. assert (not (unprotected 0)). apply not_unprotected_zero. unfold not in H. destruct H. apply Hp2.
(*external*)
apply eval_ext. 
  assert (me = ct1). apply (plug_same_memory me ct1 c11 m). apply H3. rewrite <- H8.
  assert (me' = ct2). apply (plug_same_memory me' ct2 c11 m). apply H7. rewrite <- H9. apply H0.
Qed.




(*==============================================
   Theorems  on the trace semantics
==============================================*)


Reserved Notation " L '~~~' L' " (at level 50, left associativity).

Inductive weak_equiv : list Label -> list Label -> Prop :=
| weak_tau_l : forall (ll ll' : list Label), ll ~~~ ll' -> (Tau :: ll) ~~~ ll'
| weak_tau_r : forall (ll ll' : list Label), ll ~~~ ll' -> ll ~~~ (Tau :: ll')
| weak_tick : (Tick :: nil) ~~~ (Tick :: nil)
| weak_other : forall (l : Label) (ll ll' : list Label), l <> Tick -> ll ~~~ ll' -> (l :: ll) ~~~ (l :: ll')

where "L '~~~' L'" := (weak_equiv L L') : type_scope.

Theorem dave_label_implies_trace :  
  forall (st st' : State) (c : TraceState) (l : list Label),
    c = get_trace_state st ->
    st  =~= l =~=>> st' ->
    exists l', l ~~~ l' /\
    exists c', c' = get_trace_state st /\ c == l' ==>> c'.
Proof.
Admitted.







(*
Require Import Classical.
Require Import Coq.Logic.Classical_Pred_Type. 

Theorem morgan : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  split; intros.
  destruct (classic P); destruct (classic Q); try (elim H; try (left; trivial; fail); try (right; trivial; fail); fail).
  split; trivial.

  destruct (classic P); destruct (classic Q); destruct H; red; intro; destruct H3; contradiction.
Qed.
  

Theorem non_struck_implies_a_step :
  forall (p : Address) (r: RegisterFile) (f : Flags) (ctx : MemExt) (c : MemSec),
    protected p ->
    (~ stuck_state p c)->
    exists st : State, 
      (p, r, f, plug ctx c) ---> st.
Proof.
intros p r f ctx c pro nost.
unfold stuck_state in nost. 
apply morgan in nost. destruct nost.
apply not_all_ex_not in H0. 
destruct H0.
apply NNPP in H0.
induction x.
*)


(*
Theorem soundness : 
  forall (c1 c2 : MemSec) (ts1 ts2 : TraceState) (l : list Label),
      (Unk c1) == l ==>> ts1 ->
      (Unk c2) == l ==>> ts2 ->
      contextual_equivalence c1 c2.
Proof.
intros c1 c2 ts1 ts2 l H1 H2.
red.
intros ctx Hc1 Hc2. split.
(*case ->*)
  intros Hd1. red. intros n. 
  induction n. 
  red. 
  red in Hd1. red in Hd1. specialize (Hd1 0). destruct Hd1 as [n1 Hd1]. destruct Hd1 as [p Hd1].
  destruct Hd1 as [r Hd1]. destruct Hd1 as [f Hd1]. destruct Hd1 as [ctx0 Hd1]. destruct Hd1 as [c1' Hd1].
  destruct Hd1 as [sim Hd1].
  exists (n1). exists p. exists r. exists f. exists ctx0. 
  inversion Hd1. 
  assert (H11 := plug_same_memory ctx ctx0 c1' c1 H7). 
  exists c2. split. rewrite <- H0 in sim. apply sim.
  destruct H11.
  unfold initial. subst. apply do_0.
(* *)
  assert (Heq1 := plug_same_memory ctx1 ctx c1 c H5). destruct Heq1.
  assert (Heq2 := plug_same_memory ctx'' ctx0 _ _ H10). destruct Heq2.
  subst. clear H5 H10.  
  (*  this is strange
  eexists. split. apply sim.
  unfold initial. apply do_Sn with (p' := p') (r' := r') (f' := f') (c' := c2) (ctx' := ctx'). 
  assert (unprotected p_0). unfold p_0. unfold unprotected. apply or_intror. omega.
  apply (unused_mem_sec p_0 p' r_0 r' f_0 f' ctx ctx' c1 c' c2 c2 H H6).
  *)
  admit.
  red.
  red in IHn. destruct IHn as [m IHn]. destruct IHn as [p0 IHn]. destruct IHn as [r0 IHn]. 
  destruct IHn as [f0 IHn]. destruct IHn as [ctx0 IHn]. destruct IHn as [c IHn]. 
  exists m. exists p0. exists r0. exists f0. exists ctx0. 
  destruct IHn as [H HH].
Admitted.

*)