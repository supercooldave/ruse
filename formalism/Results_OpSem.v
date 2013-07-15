Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import Labels.



(*==============================================
   Lemmas  on the labelled operational semantics
==============================================*)

Lemma unused_mem_ext :
  forall (p1 p2 : Address) (r1 r2 : RegisterFile) (f1 f2 : Flags) (ctx1 ctx2 : MemExt) (c1 c2 : MemSec) (l : Label),
    (forall (r : Address) (v : Value), l <>  Write_out r v  )->
    protected p1 ->
    protected p2 ->
    (p1,r1,f1, plug ctx1 c1) ~~ l ~~> (p2, r2, f2, plug ctx1 c2) ->
    (p1,r1,f1, plug ctx2 c1) ~~ l ~~> (p2, r2, f2, plug ctx2 c2).
Proof.
intros p1 p2 r1 r2 f1 f2 ct1 ct2 c11 c21 l neql Hp1 Hp2 Tr1.
inversion Tr1.
(*call*)
destruct H10. apply (entrypoint_is_protected) in H14. assert (not (protected p1 /\ unprotected p1)). 
apply (protected_unprotected_disjoint p1). unfold not in H15. destruct H15. split; auto.
(*ret*)
destruct H10. assert (not (protected p2 /\ unprotected p2)). 
apply (protected_unprotected_disjoint p2). unfold not in H14. destruct H14. split; auto.
(*callback*)
destruct H10. assert (not (protected p2 /\ unprotected p2)). 
apply (protected_unprotected_disjoint p2). unfold not in H17. destruct H17. split; auto.
(*retback*)
destruct H11. apply (entrypoint_is_protected) in H14. assert (not (protected p1 /\ unprotected p1)). 
apply (protected_unprotected_disjoint p1). unfold not in H15. destruct H15. split; auto.
(*writeout  contradiction*)
rewrite <- H4 in neql. unfold not in neql. destruct neql with (r := (r1 rd)) (v := (r1 rs)). reflexivity.
(*internal *)
apply los_eval_int. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). apply H3. rewrite <- H10. 
  assert (m' = c21). apply (plug_same_memory me ct1 c21 m'). apply H8. rewrite <- H11. apply H4. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H10. auto.
(*external*)
inversion H4.
  (*movl*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*movs*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*movi*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*cmp*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*add*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*sub*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*call*)
  destruct H20 as [Ha Hb]. assert (not (protected p2 /\ unprotected p2)) as Hn. 
   apply (protected_unprotected_disjoint p2). unfold not in Hn. destruct Hn. split; auto.
  (*ret*)
  destruct H20 as [Ha Hb]. assert (not (protected p2 /\ unprotected p2)) as Hn. 
   apply (protected_unprotected_disjoint p2). unfold not in Hn. destruct Hn. split; auto.
  (*je t*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*je f*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*jl t*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*jl f*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*je t*)
  destruct H20 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*halt*)
  subst. assert (not (protected 0)). apply not_protected_zero. unfold not in H. destruct H. apply Hp2.
(*tick in sec*)
  apply los_eval_int_halt. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). apply H3. rewrite <- H10. 
  assert (m' = c21). apply (plug_same_memory me ct1 c21 m'). apply H8. rewrite <- H11. apply H4. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H10. auto.
(*tick in ext*)
  inversion H4. 
  (*movl*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*movs*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*movi*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*cmp*)
  destruct H19 as [Ha Hb]. assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*add*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*sub*)
  destruct H19 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*call*)
  destruct H20 as [Ha Hb]. assert (not (protected p2 /\ unprotected p2)) as Hn. 
   apply (protected_unprotected_disjoint p2). unfold not in Hn. destruct Hn. split; auto.
  (*ret*)
  destruct H20 as [Ha Hb]. assert (not (protected p2 /\ unprotected p2)) as Hn. 
   apply (protected_unprotected_disjoint p2). unfold not in Hn. destruct Hn. split; auto.
  (*je t*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*je f*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*jl t*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*jl f*)
  destruct H21 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*je t*)
  destruct H20 as [Ha Hb].  assert (not (protected p1 /\ unprotected p1)) as Hn. 
   apply (protected_unprotected_disjoint p1). unfold not in Hn. destruct Hn. split; auto.
  (*halt*)
  subst. assert (not (protected 0)). apply not_protected_zero. unfold not in H. destruct H. apply Hp2.
Qed.



(*==============================================
   Lemmas  on the operational semantics
==============================================*)


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












