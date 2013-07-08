Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.


(*==============================================
   Operational Semantics
==============================================*)
Open Scope type_scope.



(* Operational rules *)
Reserved Notation "S '--i-->' S'" (at level 50, left associativity).

Inductive evalSec : StateSec -> StateSec -> Prop :=
| eval_sec_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : MemSec) (rd rs : Register),
  inst (lookupMS m p) (movl rd rs) -> 
  int_jump p (S p) ->
  read_allowed p  (r rs) -> 
  r' = updateR r rd (lookupMS m (r rs)) ->  
  (p, r, f, m) --i--> (S p, r', f, m)
  
| eval_sec_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : MemSec) (rd rs : Register),
  inst (lookupMS m p) (movs rd rs) -> 
  int_jump p (S p) ->
  data_segment (r rd) ->
  write_allowed p  (r rd) -> 
  m' = updateMS m  (r rd) (r rs)->  
  (p, r, f, m) --i--> (S p, r, f, m')
  
| eval_sec_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : MemSec) (rd : Register),
  inst (lookupMS m p) (movi rd i) -> 
  int_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) --i--> (S p, r', f, m)
  
| eval_sec_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : MemSec) (r1 r2 : Register),
  inst (lookupMS m p) (cmp r1 r2) -> 
  int_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) --i--> (S p, r, f', m)
  
| eval_sec_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemSec) (rd rs : Register),
  inst (lookupMS m p) (add_ rd rs) -> 
  int_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) --i--> (S p, r', f', m)
  
| eval_sec_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemSec) (rd rs : Register),
  inst (lookupMS m p) (sub_ rd rs) -> 
  int_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) --i--> (S p, r', f', m)
  
| eval_sec_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : MemSec) (rd : Register),
  inst (lookupMS m p) (call rd) -> 
  p' = lookupMS m (r rd) ->
  int_jump p p' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = updateMS m (r'' SP) (S p) ->
  (p, r, f, m) --i--> (p', r'', f, m'')
  
| eval_sec_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : MemSec),
  inst (lookupMS m p)  ret ->
  p' =  lookupMS m (r SP) ->
  int_jump p p' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) --i--> (p', r'', f, m')
  
| eval_sec_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  int_jump p p' ->
  (p, r, f, m) --i--> (p', r, f, m)
  
| eval_sec_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  int_jump p p' ->
  (p, r, f, m) --i--> (p', r, f, m)
  
| eval_sec_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  int_jump p p' ->
  (p, r, f, m) --i--> (p', r, f, m)
  
| eval_sec_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (ri : Register),
  inst (lookupMS m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  int_jump p p' ->
  (p, r, f, m) --i--> (p', r, f, m)
  
| eval_sec_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemSec) (rd : Register),
  inst (lookupMS m p) (jmp rd) -> 
  p' = r rd ->
  int_jump p p' ->
  (p, r, f, m) --i--> (p', r, f, m)
  
| eval_sec_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : MemSec),
  inst (lookupMS m p) halt ->
  (p, r, f, m) --i--> (0, r, f, m)
  
  where "S '--i-->' S'" := (evalSec S S') : type_scope.









Reserved Notation "S '--e-->' S'" (at level 50, left associativity).

Inductive evalExt : StateExt -> StateExt -> Prop :=
| eval_ext_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : MemExt) (rd rs : Register),
  inst (lookupME m p) (movl rd rs) -> 
  ext_jump p (S p) ->
  read_allowed p  (r rs) -> 
  r' = updateR r rd (lookupME m (r rs)) ->  
  (p, r, f, m) --e--> (S p, r', f, m)
  
| eval_ext_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : MemExt) (rd rs : Register),
  inst (lookupME m p) (movs rd rs) -> 
  ext_jump p (S p) ->
  write_allowed p  (r rd) -> 
  m' = updateME m  (r rd) (r rs)->  
  (p, r, f, m) --e--> (S p, r, f, m')
  
| eval_ext_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : MemExt) (rd : Register),
  inst (lookupME m p) (movi rd i) -> 
  ext_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) --e--> (S p, r', f, m)
  
| eval_ext_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : MemExt) (r1 r2 : Register),
  inst (lookupME m p) (cmp r1 r2) -> 
  ext_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) --e--> (S p, r, f', m)
  
| eval_ext_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemExt) (rd rs : Register),
  inst (lookupME m p) (add_ rd rs) -> 
  ext_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) --e--> (S p, r', f', m)
  
| eval_ext_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : MemExt) (rd rs : Register),
  inst (lookupME m p) (sub_ rd rs) -> 
  ext_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) --e--> (S p, r', f', m)
  
| eval_ext_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : MemExt) (rd : Register),
  inst (lookupME m p) (call rd) -> 
  p' = lookupME m (r rd) ->
  ext_jump p p' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = updateME m (r'' SP) (S p) ->
  (p, r, f, m) --e--> (p', r'', f, m'')
  
| eval_ext_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : MemExt),
  inst (lookupME m p)  ret ->
  p' =  lookupME m (r SP) ->
  ext_jump p p' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) --e--> (p', r'', f, m')
  
| eval_ext_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemExt) (ri : Register),
  inst (lookupME m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  ext_jump p p' ->
  (p, r, f, m) --e--> (p', r, f, m)
  
| eval_ext_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemExt) (ri : Register),
  inst (lookupME m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  ext_jump p p' ->
  (p, r, f, m) --e--> (p', r, f, m)
  
| eval_ext_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemExt) (ri : Register),
  inst (lookupME m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  ext_jump p p' ->
  (p, r, f, m) --e--> (p', r, f, m)
  
| eval_ext_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemExt) (ri : Register),
  inst (lookupME m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  ext_jump p p' ->
  (p, r, f, m) --e--> (p', r, f, m)
  
| eval_ext_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : MemExt) (rd : Register),
  inst (lookupME m p) (jmp rd) -> 
  p' = r rd ->
  ext_jump p p' ->
  (p, r, f, m) --e--> (p', r, f, m)
  
| eval_ext_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : MemExt),
  inst (lookupME m p) halt ->
  (p, r, f, m) --e--> (0, r, f, m)
  
  where "S '--e-->' S'" := (evalExt S S') : type_scope.

 