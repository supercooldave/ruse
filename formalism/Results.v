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
   Theorems  on the trace semantics
==============================================*)






(*==============================================
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)
Open Scope type_scope.

(* TODO: these should be formalised in terms of lists of labels, not just a single label. *)


Axiom correspond_lookups_protected_val :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    protected p ->
    ((lookupMS c p) = (lookup (plug ctx c) p)).
Axiom correspond_lookups_punrotected :
  forall (p : Address) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    ( (lookupME ctx p) = (lookup (plug ctx c) p)).

Axiom correspond_register_lookups_protected :
  forall (p : Address) (r : RegisterFile) (rd : Register) (c : MemSec) (ctx : MemExt) (v : Value),
    protected p ->
    (updateR r rd (lookupMS c v) = updateR r rd (lookup (plug ctx c) v)).
Axiom correspond_register_lookups_unprotected :
  forall (p : Address) (r : RegisterFile) (rd : Register) (c : MemSec) (ctx : MemExt) (v : Value),
    unprotected p ->
    (updateR r rd (lookupME ctx v) = updateR r rd (lookup (plug ctx c) v)).


Parameter get_trace_state : State -> TraceState.


Axiom update_protected : 
  forall (a : Address) (ctx : MemExt) (c :MemSec) (v : Value) (m : Memory),
    data_segment a -> 
    m = update (plug ctx c) (a) (v)-> 
    getSecMem m = updateMS c a v.

Axiom protected_pc_protected_sp : forall (a : Address) (r : RegisterFile),
  protected a ->
  protected (r SP).

Axiom unknown_taus : 
  forall (c : MemSec),
    Unk c -- Tau --> Unk c.

Theorem single_label_in_labelled_imply_same_label_in_trace : 
  forall (p : Address) (r : RegisterFile) (f : Flags) (ctx : MemExt) (c : MemSec) (l : Label) (st : State) ,
    l <> Tick ->
    (p, r, f, plug ctx c) ~~ l ~> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) -- l --> ts) \/ (Unk c) -- l --> ts).
Proof.
intros p r f ctx c l st t H. 
inversion H.
inversion H0 as [ h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15].
  (*case analysis on all possible Taus*)
    (*movl*)
    inversion H10 as [Hin | Hex].
      (*internal Tau*) 
      exists (x := Sta ((S p),r', f0, c)). apply or_introl. apply tr_intern. inversion Hin. 
       rewrite <- (correspond_lookups_protected_val p  c ctx H13) in H8. 
       rewrite <- (correspond_register_lookups_protected p r rd c ctx (r rs) H13) in H12. 
       rewrite H6.
       apply sec_eval_movl with (rs := rs) (rd := rd); auto. apply Hin.
      (*external Tau*)
      exists (x := (Unk c)). apply or_intror. apply unknown_taus.
    (*movs write in prot*) 
    exists ( x := Sta ((S p), r, f, getSecMem m')). apply or_introl. apply tr_intern.
     rewrite <- (correspond_lookups_protected_val p c ctx H12) in H8. 
     rewrite (update_protected (r rd) ctx c (r rs) m' H13 H14).  
     inversion H9.
       (*internal jump*)
       apply sec_eval_movs with (rs := rs) (rd := rd) (m := c) (m' := updateMS c (r rd) (r rs)) ; auto.
       (*external jump (contradiction)*) 
       destruct H15. assert (not (protected p /\ unprotected p)) by apply (protected_unprotected_disjoint p). destruct H17. 
        apply conj. apply H12. apply H15. 
      (*prove the internal jump*)
      destruct H9.
        (*internal*)
        apply H9.
        (*external*)
        assert (not (protected p /\ unprotected p)) by apply (protected_unprotected_disjoint p). destruct H15. 
         apply conj. apply H12. destruct H9. apply H9. 
    (*movs write in unprot *)
    exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*movi*) 
    inversion H10 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r', f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p c ctx H12) in H9. 
       apply sec_eval_movi with (rd := rd) ( i := i); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*cmp*)
    inversion H10 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r, f', c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H12) in H9. 
       apply sec_eval_compare with (r1 := r1) (r2 := r2); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*add*)
    inversion H9 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r', f', c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H14) in H8. 
       apply sec_eval_add with (rs := rs) (rd := rd) (v :=v); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*sub*)
    inversion H9 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r', f', c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H14) in H8. 
       apply sec_eval_sub with (rs := rs) (rd := rd) (v :=v); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*call same jump*)
    inversion H10 as [Hin | Hex].
      (*internal*)
      exists (x := Sta (p', r'', f, getSecMem m'')). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H15) in H8.
       apply sec_eval_call with (r':=r') (rd := rd); auto. 
      admit. admit. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*ret same jump*)
    inversion H11 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*je true*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      exists (x := Sta (p', r, f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H13) in H8.
       apply sec_eval_je_true with (ri := ri) ; auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*je false*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r, f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H13) in H8.
       apply sec_eval_je_false with (ri := ri) ; auto. rewrite <- H11. apply Hin. rewrite <- H11. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*jl true*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      exists (x := Sta (p', r, f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H13) in H8.
       apply sec_eval_jl_true with (ri := ri) ; auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*jl false*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r, f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H13) in H8.
       apply sec_eval_jl_false with (ri := ri) ; auto. rewrite <- H11. apply Hin. rewrite <- H11. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*jmp*)
    inversion H11 as [Hin | Hex].
      (*internal*)
      exists (x := Sta (p', r, f, c)). apply or_introl. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected_val p  c ctx H12) in H9.
       apply sec_eval_jump with (rd := rd) ; auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply unknown_taus.
    (*halt*)
      exists (x := Sta (0, r, f, c)).  apply or_introl. 
      admit. (*look for contradiction*)
(* ""inductive"" case: one action*)
  (*case Call*) 
  exists (x := Sta (p', r'', f, c)). apply or_intror.  apply tr_call. destruct H6; auto.    
  (*case Callback*)
  exists (x := Unk (updateMS c (r' SP) (S p))). apply or_introl. destruct H6.
   rewrite <- (correspond_lookups_protected_val p c ctx H6) in H4. 
   apply tr_callback with (r' := r') (rd := rd); auto. apply conj; auto.
  (*case Return*)
  exists (x := Unk c). apply or_introl. destruct H8.
   rewrite <- (correspond_lookups_protected_val p c ctx H8) in H4. apply tr_return with (sp := SP) ; auto. 
   assert (protected (r SP)). apply protected_pc_protected_sp with (a := p); auto.
   rewrite (correspond_lookups_protected_val (r SP) c ctx H12); auto. apply conj. apply H8. apply H11.
  (*case Returnback*)
  exists (x := Sta (p', r'', f, c)). apply or_intror. apply tr_returnback. apply H6.
  (*case Writeout*)
  exists (x := Sta ((S p), r, f, c)). apply or_introl. apply tr_writeout ; auto. inversion H5.
    apply H12.
    destruct H12. assert (not (protected p /\ unprotected p)) by apply (protected_unprotected_disjoint p). destruct H14. 
     apply conj. apply H9. apply H12.
   rewrite (correspond_lookups_protected_val p c ctx H9) ; auto.
Qed.































Theorem example_induction : 
  forall (p : Address) (r : RegisterFile) (f : Flags) (ctx : MemExt) (c : MemSec) (l : list Label) (st : State) ,
    (p, r, f, plug ctx c) =~= l =~>> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) == l ==>> ts) \/ (Unk c) == l ==>> ts).
Proof. 
intros p r f ctx c l st H. 


induction H as [Ha0 | Ha2 | Ha3 | Ha4]. 

admit.
admit.

(* here the IH has a wrong binding for t' *)

Admitted.














(* Here is a bunch of FALSE theorems, which are only temporarly Admitted
   and which i use to remember how to do things in Coq in certain cases
   *)

(*generalize H.*)
(*remember (p,r,f,plug ctx c) as t in H.*) 
(*set ( Haa := (p,r,f,plug ctx c)) in H; assert (Eq1 : t1 = (p,r,f,plug ctx c)) by reflexivity; clearbody t1.*)
(*induction H as [Ha0 | Ha2 | Ha3 | Ha4]. do not induce on l as it would bring forth a case analysis on all actions *)




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
    st  =~= l =~>> st' ->
    exists l', l ~~~ l' /\
    exists c', c' = get_trace_state st /\ c == l' ==>> c'.
Proof.
Admitted.









Axiom correspond_lookups_protected :
  forall (p : Address) (i : Instruction) (c : MemSec) (ctx : MemExt),
    protected p ->
    (inst (lookupMS c p) i <-> inst (lookup (plug ctx c) p) i).
Axiom correspond_lookups_punrotected :
  forall (p : Address) (i : Instruction) (c : MemSec) (ctx : MemExt),
    unprotected p ->
    (inst (lookupME ctx p) i <-> inst (lookup (plug ctx c) p) i).



Theorem labels_in_labelled_imply_labels_in_trace : 
  forall (p : Address) (r : RegisterFile) (f : Flags) (ctx : MemExt) (c : MemSec) (l : list Label) (st : State) ,
    (p, r, f, plug ctx c) =~= l =~>> st -> 
    exists ts: TraceState,
     (( Sta (p, r, f, c) == l ==>> ts) \/ (Unk c) == l ==>> ts).
Proof with eauto. 
intros p r f ctx c l st H. 
inversion H.
(*base case : 0 reduction step *)
exists (x := Sta (p,r,f,c)). apply or_introl. apply trace_refl.
(*inductive case: tau action*)
inversion H0 as [Hb0 | Hb1 | Hb2 | Hb3 | Hb4 | Hb5]. inversion H4. 
  (*case analysis on all possible Taus*)
    (*movl*)
    inversion H13 as [Hin | Hex].
      (*internal Tau*) 
      exists (x := Sta ((S p),r', f0, c)). apply or_introl. apply trace_tau. apply tr_intern. inversion Hin. 
       rewrite <- (correspond_lookups_protected p (movl rd rs) c ctx H16) in H11. 
       rewrite <- (correspond_register_lookups_protected p r rd c ctx (r rs) H16) in H15. 
       rewrite H9.
       apply sec_eval_movl with (rs := rs) (rd := rd); auto. apply Hin.
      (*external Tau*)
      exists (x := (Unk c)). apply or_intror. apply trace_refl.  
    (*movs write in prot*) 
    exists ( x := Sta ((S p), r, f, getSecMem m')). apply or_introl. apply trace_tau. apply tr_intern.
     rewrite <- (correspond_lookups_protected p (movs rd rs) c ctx H15) in H11. 
     rewrite (update_protected (r rd) ctx c (r rs) m' H16 H17).  
     inversion H12.
       (*internal jump*)
       apply sec_eval_movs with (rs := rs) (rd := rd) (m := c) (m' := updateMS c (r rd) (r rs)) ; auto.
       (*external jump (contradiction)*) 
       destruct H18. assert (not (protected p /\ unprotected p)) by apply (protected_unprotected_disjoint p). destruct H20. 
        apply conj. apply H15. apply H18. 
      (*prove the internal jump*)
      destruct H12.
        (*internal*)
        apply H12.
        (*external*)
        assert (not (protected p /\ unprotected p)) by apply (protected_unprotected_disjoint p). destruct H18. 
         apply conj. apply H15. destruct H12. apply H12. 
    (*movs write in unprot *)
    exists (x := Unk c). apply or_intror. apply trace_refl.
    (*movi*) 
    inversion H13 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r', f, c)). apply or_introl. apply trace_tau. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected p (movi rd i) c ctx H15) in H12. 
       apply sec_eval_movi with (rd := rd) ( i := i); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*cmp*)
    inversion H13 as [Hin | Hex].
      (*internal*)
      exists (x := Sta ((S p), r, f', c)). apply or_introl. apply trace_tau. apply tr_intern. inversion Hin.
       rewrite <- (correspond_lookups_protected p (cmp r1 r2) c ctx H15) in H12. 
       apply sec_eval_compare with (r1 := r1) (r2 := r2); auto. apply Hin.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*add*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*sub*)
    inversion H12 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*call same jump*)
    inversion H13 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*ret same jump*)
    inversion H14 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*je true*)
    inversion H15 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*je false*)
    inversion H15 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*jl true*)
    inversion H15 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*jl false*)
    inversion H15 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*jmp*)
    inversion H14 as [Hin | Hex].
      (*internal*)
      admit.
      (*ext*)
      exists (x := Unk c). apply or_intror. apply trace_refl.
    (*halt*)
      admit. (*look for contradiction*)
(*inductive case: one action followed by a list*)
  inversion H1.
  (*case Tau*)
  rewrite H8 in H0. contradiction H0. auto.
  (*case Call*) 
  exists (x := get_trace_state st). apply or_intror. apply trace_trans with (t := Unk c) (t' := Sta (p', r'', f, c)).
    rewrite H13. apply H0.
    apply tr_call. destruct H12; auto.
    
  admit.
  (*case Callback*)
  admit.
  (*case Return*)
  admit.
  (*case Returnback*)
  admit.
  (*case Writeout*)
  admit.
(*inductive case: tick*)
  exists (x := Sta (p',r',f',getSecMem m')). apply or_introl. apply trace_trans with (t' := Sta (p',r',f', getSecMem m')). 
    admit. (*this is really trivial SHIT*)
    apply tr_internal_tick. 
    (*case analysis on all steps that produce a tick*)
    (* inversion H. most cases with contradiction; halt with sth that is not contradiction*) admit.
    auto.
    apply trace_refl.
Qed.
