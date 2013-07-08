Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import Labels.
Require Import SameJumpTransitions.


(*==============================================
   Trace Semantics
==============================================*)



(* Trace semantics *)
Reserved Notation " T '--' L '-->' T' " (at level 50, left associativity).

Inductive trace : TraceState -> Label -> TraceState -> Prop :=
| tr_intern : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': MemSec),
  (p, r, f, m) --i--> (p', r', f', m') ->
  ( ~ (inst (lookupMS m p) (halt))) ->
  Sta (p, r, f, m) -- Tau --> Sta (p', r', f', m')

| tr_internal_tick : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': MemSec),
  (p, r, f, m) --i--> (p', r', f', m') ->
  (inst (lookupMS m p) (halt)) ->
  Sta (p, r, f, m) -- Tick --> Sta (p', r', f', m')

| tr_writeout : forall (p : Address) (r : RegisterFile) (f: Flags) (m: MemSec) (rd rs : Register),
  int_jump p (S p) ->
  inst (lookupMS m p ) (movs rd rs)->
  unprotected (r rd) ->
  Sta (p, r, f, m) --  Write_out (r rd) (r rs) --> Sta ( (S p), r, f, m) 

| tr_call : forall (p : Address) (r : RegisterFile) (f: Flags) (m: MemSec),
  entrypoint p ->
  (Unk m) -- Call r f p  --> Sta (p, r, f, m)

| tr_returnback : forall (p : Address) (r : RegisterFile) (f: Flags) (m: MemSec),
  return_entrypoint p ->
  (Unk m) -- Returnback r f p --> Sta (p, r, f, m)

| tr_callback : forall (p p': Address) (r r': RegisterFile) (f: Flags) (m m': MemSec) (rd : Register),
  inst (lookupMS m p) (call rd) ->
  exit_jump p p' ->
  r' = updateR r SP (S (r SP)) ->
  m' = updateMS m (r' SP) (S p)->
  Sta (p, r, f, m) -- Callback r f p' --> (Unk m')

| tr_return : forall (p p' : Address) (r : RegisterFile) (f: Flags) (m: MemSec) (sp : Register),
  inst (lookupMS m p) (ret) ->
  p' = lookupMS m (r sp) ->
  p' = address_returnback_entry_point ->
  exit_jump p p'->
  Sta (p, r, f, m) -- Return r f p' --> (Unk m)

where "T '--' L '-->' T'" := (trace T L T') : type_scope.


(* reflexive-transitive closure of the trace semantics *)
Reserved Notation " T '==' L '==>>' T' " (at level 51, left associativity).

Inductive trace_semantics_tr_ref : TraceState -> ( list Label ) -> TraceState -> Prop :=
| trace_refl : forall (t : TraceState),
  t == nil ==>> t

| trace_tau : forall (t t' : TraceState),
  t -- Tau --> t' ->
  t == nil ==>> t'

| trace_trans : forall (t t' t'' : TraceState) (l : Label) (l' : list Label),
  ~ (l = Tau) ->
  t -- l --> t' ->
  t' == l' ==>> t''->
  t == cons l l' ==>> t''

where "T '==' L '==>>' T'" := (trace_semantics_tr_ref T L T') : type_scope.







