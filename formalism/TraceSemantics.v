Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import Labels.


(*==============================================
   Trace Semantics
==============================================*)


(* Evaluation step in protected memory only*)
Reserved Notation " T '----->' T' " (at level 50, left associativity).

Inductive eval_sec_t : StateSec -> StateSec -> Prop :=
| sec_eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : MemSec) (rd rs : Register),
  inst (lookupMS m p) (movl rd rs) -> 
  int_jump p (S p) ->
  read_allowed p  (r rs) -> 
  r' = updateR r rd (lookupMS m (r rs)) ->  
  (p, r, f, m) -----> (S p, r', f, m)
  
| sec_eval_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : MemSec) (rd rs : Register),
  inst (lookupMS m p) (movs rd rs) -> 
  int_jump p (S p) ->
  protected p -> 
  data_segment (r rd) ->
  m' = updateMS m  (r rd) (r rs)->  
  (p, r, f, m) -----> (S p, r, f, m')
  
| sec_eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : MemSec) (rd : Register),
  inst (lookupMS m p) (movi rd i) -> 
  int_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) -----> (S p, r', f, m)
  
| sec_eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : MemSec) (r1 r2 : Register),
  inst (lookupMS m p) (cmp r1 r2) -> 
  int_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) -----> (S p, r, f', m)
  
| sec_eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemSec) (rd rs : Register),
  inst (lookupMS m p) (add_ rd rs) -> 
  int_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) -----> (S p, r', f', m)
  
| sec_eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemSec) (rd rs : Register),

  inst (lookupMS m p) (sub_ rd rs) -> 
  int_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) -----> (S p, r', f', m)
  
| sec_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : MemSec) (rd : Register),
  inst (lookupMS m p) (call rd) -> 
  p' = lookupMS m (r rd) ->
  int_jump p p' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = updateMS m (r'' SP) (S p) ->
  (p, r, f, m) -----> (p', r'', f, m'')
  
| sec_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : MemSec),
  inst (lookupMS m p)  ret ->
  p' =  lookupMS m (r SP) ->
  int_jump p p' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) -----> (p', r'', f, m')
  
| sec_eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  int_jump p p' ->
  (p, r, f, m) -----> (p', r, f, m)
  
| sec_eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  int_jump p p' ->
  (p, r, f, m) -----> (p', r, f, m)
  
| sec_eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  int_jump p p' ->
  (p, r, f, m) -----> (p', r, f, m)
  
| sec_eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  int_jump p p' ->
  (p, r, f, m) -----> (p', r, f, m)
  
| sec_eval_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (rd : Register),
  inst (lookupMS m p) (jmp rd) -> 
  p' = r rd ->
  int_jump p p' ->
  (p, r, f, m) -----> (p', r, f, m)
  
| sec_eval_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : MemSec),
  inst (lookupMS m p) halt ->
  (p, r, f, m) -----> (0, r, f, m)

  where "S '----->' S'" := (eval_sec_t S S') : type_scope.






(* Trace semantics *)
Reserved Notation " T '--' L '-->' T' " (at level 50, left associativity).

Inductive trace : TraceState -> Label -> TraceState -> Prop :=
| tr_intern : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': MemSec),
  (p, r, f, m) -----> (p', r', f', m') ->
  int_jump p p' ->
  Sta (p, r, f, m) -- Tau --> Sta (p', r', f', m')

| tr_internal_tick : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': MemSec),
  (p, r, f, m) -----> (p', r', f', m') ->
  stuck_state p' m' ->
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
(*  r'' = updateR r' SP (S (r' SP)) ->  ?? should this be on the traces? *)
  Sta (p, r, f, m) -- Callback r f p' --> (Unk m')

| tr_return : forall (p p' : Address) (r : RegisterFile) (f: Flags) (m: MemSec) (sp : Register),
  p' = lookupMS m (r sp) ->
  exit_jump p p'->
  inst (lookupMS m p) (ret) ->
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







