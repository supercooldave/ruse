
(* Temporary home for these *)




Definition contextual_equivalence : Program -> Program -> Prop := fun p1 p2 : Program => 
  forall c : Context, compatible p1 c -> compatible p2 c ->
    ( (diverge (initial (plug p1 c))) <-> (diverge (initial (plug p2 c))) ).
  



(*==============================================
   Theorems  on the trace semantics
==============================================*)

(* TODO : requires interface preservation lemma *)
Lemma trace_semantics_soundness :
  forall p1 p2: Program, trace_equivalence p1 p2 -> contextual_equivalence p1 p2.
Proof.
Admitted.

(* TODO *)
Lemma trace_semantics_completeness :
  forall p1 p2: Program, contextual_equivalence p1 p2 -> trace_equivalence p1 p2.
Proof.
Admitted.

Theorem fully_abstract_trace_semantics : 
  forall p1 p2 : Program, contextual_equivalence p1 p2 <-> trace_equivalence p1 p2.
Proof.
intros.
split.
apply trace_semantics_completeness.
apply trace_semantics_soundness.
Qed.



(*==============================================
   Theorems  on the labelled operational semantics
==============================================*)


Lemma labelled_semantics_implies_original :
  forall (s1 s2 : State) (l : Label),
    s1 ~~ l ~> s2 ->
    s1 ---> s2.
Proof.
intros.
destruct H. destruct H; auto. 
apply eval_movl with (rs := rs) (rd := rd); auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
apply eval_movi with (i := i) (rd := rd); auto.
apply eval_compare  with (r1 := r1) (r2 := r2); auto.
apply eval_add with (rs := rs) (rd := rd) (v := v); auto.
apply eval_sub with (rs := rs) (rd := rd) (v := v); auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_introl ; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_introl; auto.
apply eval_je_true with (ri := ri); auto.
apply eval_je_false with (ri := ri); auto.
apply eval_jl_true with (ri := ri); auto.
apply eval_jl_false with (ri := ri); auto.
apply eval_jump with (rd := rd); auto.
apply eval_halt; auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_intror. apply or_introl; auto.
apply eval_call with (r' := r') (r'' := r'') (m' := m') (m'' := m'') (rd := rd); auto. apply or_intror. apply or_intror; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_intror. apply or_intror; auto.
apply eval_ret with (r' := r') (r'' := r'') (m' := m'); auto. apply or_intror; auto.
apply eval_movs with (rs := rs) (rd := rd); auto.
Qed.


(* TODO: besides the problem with the admits, i don't know how to call the other labels into place
 there should be  5 more cases generated for them (writeout, call callback return returnback) *)
Lemma original_semantics_implies_labelled :
  forall s1 s2 : State,
    s1 ---> s2 ->
    exists l : Label, s1 ~~ l ~> s2.
Proof.
intros.
destruct H. 
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movl with (rs := rs) (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. 

apply sd_eval_movs_prot with (rs := rs) (rd := rd); auto.


admit. (* big problem. i get an address A, and the proof has (r rd), and i don't know how to unify them *)
Admitted. 

(*
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_movi with (i := i) (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_compare with (r1 := r1) (r2 := r2); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_add with (rs := rs) (rd := rd) (v := v); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_sub with (rs := rs) (rd := rd) (v := v); auto.
admit.
admit.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_je_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_true with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jl_false with (ri := ri); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_jump with (rd := rd); auto.
apply ex_intro with (x := Tau). apply los_eval_same. apply sd_eval_halt; auto.
Qed.

*)






