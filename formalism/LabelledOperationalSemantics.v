Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import Labels.



(*==============================================
   Labelled Operational Semantics
==============================================*)

(* rules for reduction across the same domain (prot - prot) or (unprot - unprot) *)
Reserved Notation "S '~~>' S'" (at level 50, left associativity).

Inductive eval_same_dom : State -> State -> Prop :=
| sd_eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
  inst (lookup m p) (movl rd rs) -> 
  same_jump p (S p) ->
  read_allowed p (r rs) -> 
  r' = updateR r rd (lookup m (r rs)) ->  
  (p, r, f, m) ~~> (S p, r', f, m)
    
| sd_eval_movs_prot : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) -> 
  protected p->
  data_segment (r rd)->
  m' = update m (r rd) (r rs) ->  
  (p, r, f, m) ~~> (S p, r, f, m')

| sd_eval_movs_unprot : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) -> 
  unprotected p->
  unprotected (r rd)->
  m' = update m (r rd) (r rs) ->  
  (p, r, f, m) ~~> (S p, r, f, m')
    
| sd_eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (movi rd i) -> 
  same_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) ~~> (S p, r', f, m)
  
| sd_eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : Memory) (r1 r2 : Register),
  inst (lookup m p) (cmp r1 r2) -> 
  same_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) ~~> (S p, r, f', m)
  
| sd_eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (add_ rd rs) -> 
  same_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ~~> (S p, r', f', m)
  
| sd_eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (sub_ rd rs) -> 
  same_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ~~> (S p, r', f', m)
  
| sd_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  same_jump p p' ->  (*only jumps between the same domains*)
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~> (p', r'', f, m'')
  
| sd_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  same_jump p p' -> (* only jumps between the same domains*)
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~> (p', r'', f, m')
  
| sd_eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (jmp rd) -> 
  p' = r rd ->
  same_jump p p' ->
  (p, r, f, m) ~~> (p', r, f, m)
  
| sd_eval_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : Memory),
  inst (lookup m p) halt ->
  (p, r, f, m) ~~> (0, r, f, m)
  
  where "S '~~>' S'" := (eval_same_dom S S') : type_scope.


(* rules for reduction that cross a domain, effectively creating a label *)
Reserved Notation "S '~~' L '~>' S'" (at level 50, left associativity).

Inductive eval_label : State -> Label -> State -> Prop :=
| los_eval_same : forall (s s' : State),
  s ~~> s'->
  s ~~ Tau ~> s'

| los_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  entry_jump p p' ->  
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~ Call r'' f p' ~> (p', r'', f, m'')

| los_eval_callback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  exit_jump p p' ->  
  r' = updateR r SP (S (r SP)) ->
  m' = update m (r' SP) (S p)->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = (update m' (r'' SP) (address_returnback_entry_point)) ->
  (p, r, f, m) ~~ Callback r f p' ~> (p', r'', f, m'')

| los_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  exit_jump p p' -> 
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Return r f p'~> (p', r'', f, m')
  
| los_eval_retback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  p' = address_returnback_entry_point ->
  entry_jump p p' -> 
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Returnback r'' f p'~> (p', r'', f, m')

| los_eval_writeout : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p (r rd) ->
  protected p->
  unprotected (r rd)->
  m' = update m (r rd) (r rs) ->  
  (p, r, f, m) ~~ Write_out (r rd) (r rs) ~> (S p, r, f, m')

  where "S '~~' L '~>' S'" := (eval_label S L S') : type_scope.


Reserved Notation "S '=~=' L '=~>>' S'" (at level 50, left associativity).

Inductive eval_trace : State -> list Label -> State -> Prop :=
| lbl_trace_refl : forall (t : State),
  t =~= nil =~>> t

| lbl_trace_tau : forall (t t' : State),
  t ~~ Tau ~> t' ->
  t =~= nil =~>> t'

| lbl_trace_trans : forall (t t' t'' : State) (l : Label) (l' : list Label),
  ~ (l = Tau) ->
  t ~~ l ~> t' ->
  t' =~= l' =~>> t''->
  t =~= cons l l' =~>> t''

| lbl_trace_internal_tick : forall (p p' : Address) (r r' : RegisterFile) (f f': Flags) (m m': Memory),
  (p, r, f, m) ~~> (p', r', f', m') ->
  stuck_state p' (getSecMem m') ->
  (p, r, f, m) =~= cons Tick nil =~>> (p', r', f', m')

where "T '=~=' L '=~>>' T'" := (eval_trace T L T') : type_scope.