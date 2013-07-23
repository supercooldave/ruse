Require Import List.
Require Import Omega.

Require Import MachineModel.
Require Import Assembler.
Require Import Labels.
Require Import SameJumpTransitions.


(*==============================================
   Labelled Operational Semantics
==============================================*)


(* rules for reduction that cross a domain, effectively creating a label *)
Reserved Notation "S '~~' L '~~>' S'" (at level 50, left associativity).

Inductive eval_label : State -> Label -> State -> Prop :=
  
| los_eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  entry_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ~~ Call r'' f p' ~~> (p', r'', f, m'')
  
| los_eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' =  lookup m (r SP) ->
  exit_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Return r f p' ~~> (p', r'', f, m')
  
| los_eval_callback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = lookup m (r rd) ->
  exit_jump p p' ->
  r' = updateR r SP (S (r SP)) ->
  m' = update m (r' SP) (S p)->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = (update m' (r'' SP) (address_returnback_entry_point)) ->
  (p, r, f, m) ~~ Callback r f p' ~~> (p', r'', f, m'')
  
| los_eval_retback : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' =  lookup m (r SP) ->
  p' = address_returnback_entry_point ->
  entry_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ~~ Returnback r'' f p' ~~> ( p', r'', f, m')

| los_eval_writeout : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  int_jump p (S p) ->
  unprotected (r rd) ->
  m' = update m  (r rd) (r rs)->  
  (p, r, f, m) ~~ Write_out (r rd) (r rs) ~~> ((S p), r, f, m')

| los_eval_int : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m m' : MemSec) (me : MemExt) ,
  (p, r, f, m) --i--> (p', r', f', m') ->
  ( ~ (inst (lookupMS m p) (halt))) ->
  (p, r, f, (plug me m)) ~~ Tau ~~> (p', r', f', (plug me m'))

| los_eval_ext : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m : MemSec) (me me' : MemExt) ,
  (p, r, f, me) --e--> (p', r', f', me') ->
  ( ~ (inst (lookupME me p) (halt))) ->
  (p, r, f, (plug me m)) ~~ Tau ~~> (p', r', f', (plug me' m))  

| los_eval_int_halt : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m m' : MemSec) (me : MemExt) ,
  (p, r, f, m) --i--> (p', r', f', m') ->
  (inst (lookupMS m p) (halt)) ->
  (p, r, f, (plug me m)) ~~ Tick ~~> (p', r', f', (plug me m'))

| los_eval_ext_halt : forall (p p' : Address) (r r' : RegisterFile) (f f' : Flags) (m : MemSec) (me me' : MemExt) ,
  (p, r, f, me) --e--> (p', r', f', me') ->
  (inst (lookupME me p) (halt)) ->
  (p, r, f, (plug me m)) ~~ Tick ~~> (p', r', f', (plug me' m))  

  where "S '~~' L '~~>' S'" := (eval_label S L S') : type_scope.


Reserved Notation "S '=~=' L '=~=>>' S'" (at level 50, left associativity).




Inductive eval_trace : State -> list Label -> State -> Prop :=
| lbl_trace_refl : forall (t : State),
  t =~= nil =~=>> t

| lbl_trace_tau : forall (t t' : State),
  t ~~ Tau ~~> t' ->
  t =~= nil =~=>> t'

| lbl_trace_trans : forall (t t' t'' : State) (l : Label) (l' : list Label),
  ~ (l = Tau) ->
  t ~~ l ~~> t' ->
  t' =~= l' =~=>> t''->
  t =~= cons l l' =~=>> t''

where "T '=~=' L '=~=>>' T'" := (eval_trace T L T') : type_scope.








