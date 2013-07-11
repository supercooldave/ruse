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
   Theorems  on the trace semantics 
    and the labelled operational semantics
==============================================*)
Open Scope type_scope.

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
   rewrite <- (correspond_lookups_protected_val p c ctx H8) in H4. apply tr_return with (sp := SP) ; auto. 
   assert (protected (r SP)). apply protected_pc_protected_sp with (a := p); auto.
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
inversion H6 as [ h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14].
  (*case analysis on all possible Taus*)
    (*movl*)
    inversion H17 as [Hin]. 
      exists (x := Sta ((S p),r', f0, c)). apply or_introl. apply tr_intern. inversion H20. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H21. apply H7. 
    (*movs write in prot*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p) ,r, f0, m')). apply or_introl. apply tr_intern. subst. assert (c = m). 
       apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H22. apply H7. 
    (*movi*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p) ,r', f, m')). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*cmp*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p) ,r, f', m')). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*add*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p) ,r', f', c)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H22. apply H7. 
    (*sub*)
    inversion H17 as [Hin].
      exists (x := Sta ((S p) ,r', f', c)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H22. apply H7. 
    (*call same jump*)
    inversion H17 as [Hin]. 
      exists (x := Sta (p' ,r', f, m')). apply or_introl. apply tr_intern. subst. assert (c = m). 
       apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H21. apply H7. 
    (*ret same jump*)
    inversion H17 as [Hin]. 
      exists (x := Sta (p' ,r', f, m')). apply or_introl. apply tr_intern. subst. assert (c = m). 
       apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*je true*)
    inversion H17 as [Hin]. 
      exists (x := Sta (p' ,r, f, m)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*je false*)
    inversion H17 as [Hin]. 
      exists (x := Sta ( (S p) ,r, f, m)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*jl true*)
    inversion H17 as [Hin]. 
      exists (x := Sta (p' ,r, f, m)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*jl false*)
    inversion H17 as [Hin]. 
      exists (x := Sta ((S p) ,r, f, m)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H20. apply H7. 
    (*jmp*)
    inversion H17 as [Hin]. 
      exists (x := Sta (p' ,r, f, m)). apply or_introl. apply tr_intern. subst. assert (c = m'). 
       apply (plug_same_memory ctx me m' c). rewrite H4. reflexivity. rewrite H0. apply H6.
       assert (c = m). apply (plug_same_memory ctx me m c). rewrite H4. reflexivity. rewrite H19. apply H7. 
    (*halt*)
      exists (x := Sta (0, r, f, c)).  apply or_introl. subst. contradiction. 
(* Taus  external*) 
  exists (x := Unk c). apply or_intror. apply unknown_taus.
(* Tick internal*) 
  exists (x := Sta (0, r, f, c)). apply or_introl. apply tr_internal_tick. 
    apply eval_sec_halt; assert (c = m). apply (plug_same_memory ctx me m c); rewrite H4; reflexivity. rewrite H8. apply H7. 
    assert (c = m). apply (plug_same_memory ctx me m c); rewrite H4; reflexivity. rewrite H8. apply H7.
(* Tick external*)
  exists (x := Unk c). apply or_intror. apply unknown_ticks.
Qed.
