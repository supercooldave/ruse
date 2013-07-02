
Require Import List.
Require Import Labels.
Require Import MachineModel.

Require Import Coq.FSets.FMaps.
Require Export FMapAVL.
(*Require Export Coq.Structures.OrderedTypeEx. *)


(* This serves as an intermediate data structure between a trace from the 
   trace semantics and the code that implements the context capable of
   producing the trace. *)

(* First note that any trace is well-bracketed, or can be made to be so, 
   which means that each call has a corresponding return and calls and returns
   are properly nested. *)

(* The proof of soundness, namely two guys are not trace equivalent means that 
   are not contextually equivalent, requires that a context be produced for
   a given pair of traces. A simpler approach is to start with a single trace
   and try to find a context that produces it. *)

(* The first step is to produce an element of the corresponding data structure
   for the given trace. The data structure includes the following information:
   - the target of the call etc
   - the step number
   - the sequencing of instructions (abstracting what occurs in a method)
   - the bracketing
*)

(* Second step is to take the produced element of the data structure and use
   it as the basis for generating code. The theorem then is that the generated
   code produces the trace encoded in the data structure -- and also that
   the data structure encodes the trace. *)

(* The idea is that the separation makes it easier to manage the production of
   code corresponding to the context. And that the additional structure inferred
   can help with the proof and construction of code. *)

(* See, for instance, Martin Steffen's Habilitation thesis for a similar, if not
   identical approach. *)



Module M := FMapAVL.Make(Nat_as_OT).

Definition LabelMatrix := M.t (M.t Label).
Definition empty : LabelMatrix := M.empty (M.t Label).
(* Convert 
Definition find k (m: map_nat_nat) := M.find k m.
*)

Definition update (m: LabelMatrix) (a : Address) (step : nat) (l : Label) :=
  match M.find a m with
  | None => M.add a (M.add step l (M.empty Label)) m
  | Some n => M.add a (M.add step l n) m
  end.
  

Fixpoint build_help(m : LabelMatrix) (trace : list Label) (step : nat) :=
    match trace with
      | nil => m
      | l :: trace' =>
        (match l with
        | Tau => build_help m trace' (S step) 
        | Tick => build_help m trace' (S step) 
        | Write_out a v  => build_help (update m a step l) trace' (S step)
        | Call r f a     => build_help (update m a step l) trace' (S step)
        | Callback r f a => build_help (update m a step l) trace' (S step)
        | Return r f a   => build_help (update m a step l) trace' (S step)
        | Returnback r f a => build_help (update m a step l) trace' (S step)
          end)
    end.

Definition build (trace : list Label) : LabelMatrix 
  := build_help empty trace 0.




