Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import TraceSemantics.
Require Import OperationalSemantics.
Require Import SameJumpTransitions.
Require Import LabelledOperationalSemantics.
Require Import Labels.
Require Import MyTactics.



(*==============================================
   Lemmas  on the trace semantics
==============================================*)









(*==============================================
   Theorems  ON the trace semantics
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





Theorem fully_abstract_trace_semantics :
  forall (c1 c2 : MemSec) (l : list Label) (ctx : MemExt),
    (trace_equivalence c1 c2 l) <-> (contextual_equivalence c1 c2 ctx).
Proof.
split; intros H. 
red. intros com1 com2. split. intros Div1. red. 
induction n.
red.
red in Div1. specialize (Div1 0).  red in Div1. destruct Div1 as [n' Div1].
destruct Div1 as [p Div1].
destruct Div1 as [r Div1].
destruct Div1 as [f Div1].
destruct Div1 as [ctx0 Div1].
destruct Div1 as [c10 Div1]. 
destruct Div1 as [and Div1]. 
exists n'. exists p. exists r. exists f. exists ctx0. exists c2.
split.
apply and.
inversion Div1.
unfold initial. assert (ctx = ctx0). apply (plug_same_memory ctx ctx0 c10 c1); apply H6. rewrite H2. apply do_0.
unfold initial. 
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