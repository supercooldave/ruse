Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import OperationalSemantics.


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





Lemma unused_mem_ext :
  forall (p1 p2 : Address) (r1 r2 : RegisterFile) (f1 f2 : Flags) (ctx1 ctx2 : MemExt) (c11 c21 : MemSec),
    protected p1 ->
    protected p2 ->
    (p1,r1,f1, plug ctx1 c11) ---> (p2, r2, f2, plug ctx1 c21) ->
    (p1,r1,f1, plug ctx2 c11) ---> (p2, r2, f2, plug ctx2 c21).
Proof.