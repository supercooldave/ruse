Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import SameJumpTransitions.


(*==============================================
   Operational Semantics
==============================================*)
Open Scope type_scope.



(* Operational rules *)
Reserved Notation "S '--->' S'" (at level 50, left associativity).

Inductive evalR : State -> State -> Prop :=
  
| eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  entry_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ---> (p', r'', f, m'')
  
| eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' =  lookup m (r SP) ->
  exit_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ---> (p', r'', f, m')
  
| eval_callback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  exit_jump p p' ->
  r' = updateR r SP (S (r SP)) ->
  m' = update m (r' SP) (S p)->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = (update m' (r'' SP) (address_returnback_entry_point)) ->
  (p, r, f, m) ---> (p', r'', f, m'')
  
| eval_retback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' =  lookup m (r SP) ->
  p' = address_returnback_entry_point ->
  entry_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ---> ( p', r'', f, m')

| eval_writeout : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  int_jump p (S p) ->
  unprotected (r rd) -> 
  m' = update m  (r rd) (r rs)->  
  (p, r, f, m) ---> (S p, r, f, m')

| eval_int : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m m' : MemSec) (me : MemExt) ,
  (p, r, f, m) --i--> (p', r', f', m') ->
  (p, r, f, (plug me m)) ---> (p', r', f', (plug me m'))

| eval_ext : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m : MemSec) (me me' : MemExt) ,
  (p, r, f, me) --e--> (p', r', f', me') ->
  (p, r, f, (plug me m)) ---> (p', r', f', (plug me' m))  

  where "S '--->' S'" := (evalR S S') : type_scope.






(* Inspired by some work of Benton *)

Inductive do_n_steps: State -> nat -> State -> Prop :=
| do_0 : forall sta, do_n_steps sta 0 sta
| do_Sn : forall n (p p' p'' : Address) (r r' r'' : RegisterFile) (f f' f'' : Flags) (c c' c'' : MemSec) (ctx ctx' ctx'' : MemExt), 
  (p, r, f, plug ctx c) ---> (p', r', f', plug ctx' c') ->
  do_n_steps  (p', r', f', plug ctx' c') n  (p'', r'', f'', plug ctx'' c'') ->
  do_n_steps  (p, r, f, plug ctx c) (S n) (p'', r'', f'', plug ctx'' c'').

Definition anysteps (n : nat) (sta  : State) := 
  exists n' : nat , exists p : Address, exists r : RegisterFile, exists f : Flags, exists ctx : MemExt, exists c : MemSec,
      n' >= n /\ (do_n_steps sta n' (p, r, f, (plug ctx c))).

Definition diverge (sta : State) := forall n, anysteps n sta.



Definition contextual_equivalence (p1 p2 : MemSec) (c : MemExt) :=
    compatible p1 c -> compatible p2 c ->
    ( (diverge (initial p1 c)) <-> (diverge (initial p2 c)) ).
  





