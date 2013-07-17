Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import Labels.
Require Import MyTactics.



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
contradiction_by_jump.
(*ret*) 
contradiction_by_jump.
(*callback*)
contradiction_by_jump.
(*retback*)
contradiction_by_jump.
(*writeout  contradiction*)
rewrite <- H4 in neql. unfold not in neql. destruct neql with (r := (r1 rd)) (v := (r1 rs)). reflexivity.
(*internal *)
apply los_eval_int.  
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H10. 
  assert (m' = c21). apply (plug_same_memory me ct1 c21 m'). auto. rewrite <- H11. auto. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H10. auto.
(*external*)
inversion H4; contradiction_by_jump.
(*tick in sec*)
  apply los_eval_int_halt. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). apply H3. rewrite <- H10. 
  assert (m' = c21). apply (plug_same_memory me ct1 c21 m'). apply H8. rewrite <- H11. apply H4. 
  assert (m = c11). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H10. auto.
(*tick in ext*)
  inversion H4; contradiction_by_jump.
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
contradiction_by_jump.
(*ret*)
contradiction_by_jump.
(*callback*)
contradiction_by_jump.
(*retback*)
contradiction_by_jump.
(*writeout*)
contradiction_by_jump.
(*internal *)  
inversion H0; contradiction_by_jump.
(*external*)
apply eval_ext. 
  assert (me = ct1). apply (plug_same_memory me ct1 c11 m). auto. rewrite <- H8.
  assert (me' = ct2). apply (plug_same_memory me' ct2 c11 m). auto. rewrite <- H9. auto.
Qed.












