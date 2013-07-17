Require Import List.
Require Import Omega.

Require Import Assembler.
Require Import MachineModel.
Require Import Labels.
Require Import SameJumpTransitions.
Require Import OperationalSemantics.
Require Import LabelledOperationalSemantics.
Require Import TraceSemantics.


(* Reach a contradiction where you are assuming that the same address is 
   protected and unprotected or viceversa
   or protected and 0 or unprotected and 0
*)
Ltac shorten_contradiction_jump :=
  match goal with
    | [ H' : protected ?X , H'' : unprotected ?X |- _ ] =>
      (assert (not (protected X /\ unprotected X)) as Hn;
        [ apply (protected_unprotected_disjoint X) | unfold not in Hn; destruct Hn; split; auto] )
  end.

(*browse through all cases where a contradiction on the protected/unprotected is reachable and nail it *)
Ltac contradiction_by_jump :=
  match goal with
    | [ H' : int_jump ?X ?Y  |- _ ] => destruct H' as [Ha Hb]; shorten_contradiction_jump
    | [ H' : ext_jump ?X ?Y  |- _ ] => destruct H' as [Ha Hb]; shorten_contradiction_jump
    | [ H' : protected ?X  |- _ ] => 
      match goal with
        | [ H : 0 = X |- _] =>
          ( subst; assert (not (protected 0)) as Hn; [ apply not_protected_zero | unfold not in Hn; destruct Hn; auto])
      end
    | [ H' : unprotected ?X  |- _ ] => 
      match goal with
        | [H : 0 = X |- _] =>
          ( subst; assert (not (unprotected 0)) as Hn; [ apply not_unprotected_zero | unfold not in Hn; destruct Hn; auto])
      end
    | [ H' : entry_jump ?X ?Y |- _ ] => 
      destruct H' as [Ha Hb]; try (apply (entrypoint_is_protected) in Hb); shorten_contradiction_jump 
    | [ H' : exit_jump ?X ?Y |- _ ] => 
      destruct H' as [Ha Hb]; try (apply (entrypoint_is_protected) in Hb); shorten_contradiction_jump
  end.



(* Extract the second argument of a generic function with 2 arguments (H) and save it as id *)
Ltac grab_2nd_argument H id :=
  match goal with
  | [ H' : _ _ ?X  |- _ ]    => 
    match H with
      | H' => remember X as id
    end
  end.


(*
Ltac trivial_different_instruction :=
  match goal with
    | [ H' : inst ?X halt |- _ ] =>
      match goal with
        | [ H'' : inst X ?Y |- _ ] => 
          match ?Y with
            | halt => idtac
            | ?Z => 
              ( grab_2nd_argument H'' j; apply (no_halt_sec m' p j) in H''; unfold not in H''; destruct H''; apply H'; rewrite Heqj; intro; discriminate)
          end 
      end
  end. 
*)