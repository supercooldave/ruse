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
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)


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
   rewrite <- (correspond_lookups_protected_val p c ctx H8) in H4. 
   apply tr_return with (sp := SP); auto. 
   assert (protected (r SP)). destruct H9; try (contradiction_by_jump). auto.
   auto.
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
inversion H6; try( generate_tau_from_internal_los_step; fail). 
(*hlat*)
subst; contradiction.
(* Taus  external*) 
  exists (x := Unk c). apply or_intror. apply unknown_taus.
(* Tick internal*) 
  exists (x := Sta (0, r, f, c)). apply or_introl. apply tr_internal_tick.  
    apply eval_sec_halt;
    assert (Hn : c = m) by (apply (plug_same_memory ctx me m c); rewrite H4; reflexivity); rewrite Hn; auto. 
    assert (Hn : c = m) by (apply (plug_same_memory ctx me m c); rewrite H4; reflexivity); rewrite Hn; auto. 
(* Tick external*)
  exists (x := Unk c). apply or_intror. apply unknown_ticks.
Qed.











