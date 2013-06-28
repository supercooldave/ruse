Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import OperationalSemantics.  



(*==============================================
   Trace Semantics
==============================================*)


(* Trace semantics *)
Reserved Notation " T '--' L '-->' T' " (at level 50, left associativity).

Inductive trace : TraceState -> Label -> TraceState -> Prop :=
| tr_intern : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': Memory),
  (p, r, f, m) ---> (p', r', f', m') ->
  int_jump p p' ->
  Sta (p, r, f, m) -- Tau --> Sta (p', r', f', m')

| tr_internal_tick : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': Memory),
  (p, r, f, m) ---> (p', r', f', m') ->
  stuck_state p' m' ->
  Sta (p, r, f, m) -- Tick --> Sta (p', r', f', m')

| tr_writeout : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory) (rd rs : Register),
  int_jump p (S p) ->
  inst (lookup m p ) (movs rd rs)->
  unprotected (r rd) ->
  Sta (p, r, f, m) --  Write_out (r rd) (r rs) --> Sta ( (S p), r, f, m) 

| tr_call : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory),
  entrypoint p ->
  (Unk m) -- Call r f p  --> Sta (p, r, f, m)

| tr_returnback : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory),
  return_entrypoint p ->
  (Unk m) -- Returnback r f  --> Sta (p, r, f, m)

| tr_callback : forall (p : Address) (r : RegisterFile) (f: Flags) (m: Memory) (rd : Register),
  inst (lookup m p) (call rd) ->
  exit_jump p (lookup m (r rd)) ->
  Sta (p, r, f, m) -- Callback r f (lookup m (r rd)) --> (Unk m)

| tr_return : forall (p p' : Address) (r : RegisterFile) (f: Flags) (m: Memory) (sp : Register),
  p' = (r sp) ->
  exit_jump p p'->
  inst (lookup m p) (ret) ->
  Sta (p, r, f, m) -- Return r f  --> (Unk m)

where "T '--' L '-->' T'" := (trace T L T') : type_scope.


(* reflexive-transitive closure of the trace semantics *)
Reserved Notation " T '==' L '==>>' T' " (at level 51, left associativity).

Inductive trace_semantics : TraceState -> ( list Label ) -> TraceState -> Prop :=
| trace_refl : forall (t : TraceState),
  t == nil ==>> t

| trace_tau : forall (t t' : TraceState),
  t -- Tau --> t' ->
  t == nil ==>> t'

| trace_trans : forall (t t' t'' : TraceState) (l : Label) (l' : list Label),
  t -- l --> t' ->
  t' == l' ==>> t''->
  t == cons l l' ==>> t''

where "T '==' L '==>>' T'" := (trace_semantics T L T') : type_scope.




(*TODO  change the definition to consider only secure programs, not whole programs like now *)
Definition trace_equivalence : Program -> Program -> Prop :=
  fun p1 p2 : Program => forall p1' p2' : TraceState, forall l1 : list Label, 
    Sta (initial p1) == l1 ==>> p1' <->
    Sta (initial p2) == l1 ==>> p2'.



