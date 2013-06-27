Require Import List.
Require Import Omega.
Require Import MachineModel.
Require Import Assembler.


(*==============================================
   Operational Semantics
==============================================*)
Open Scope type_scope.

(* State of the operational semantics *)
Definition State := Address * RegisterFile * Flags * Memory.

Parameter inst : Value -> Instruction -> Prop.

(*Some axiom stating that each decoded value is unique. *)
Axiom inst_unique_encode : forall (v : Value) (i i' : Instruction), inst v i -> inst v i' -> i = i'.
Axiom inst_unique_decode : forall (v v' : Value) (i : Instruction), inst v i -> inst v' i -> v = v'.
Axiom inst_no_zero : ~ exists i : Instruction, inst 0 i.

(* Operational rules *)
Reserved Notation "S '--->' S'" (at level 50, left associativity).

Inductive evalR : State -> State -> Prop :=
| eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
  inst (lookup m p) (movl rd rs) -> 
  same_jump p (S p) ->
  read_allowed p  (r rs) -> 
  r' = updateR r rd (lookup m (r rs)) ->  
  (p, r, f, m) ---> (S p, r', f, m)
  
| eval_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
  inst (lookup m p) (movs rd rs) -> 
  same_jump p (S p) ->
  write_allowed p  (r rd) -> 
  m' = update m  (r rd) (r rs)->  
  (p, r, f, m) ---> (S p, r, f, m')
  
| eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (movi rd i) -> 
  same_jump p (S p) ->
  r' = updateR r rd i ->  
  (p, r, f, m) ---> (S p, r', f, m)
  
| eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : Memory) (r1 r2 : Register),
  inst (lookup m p) (cmp r1 r2) -> 
  same_jump p (S p) ->
  f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
  (p, r, f, m) ---> (S p, r, f', m)
  
| eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (add_ rd rs) -> 
  same_jump p (S p) ->
  v = plus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ---> (S p, r', f', m)
  
| eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
  inst (lookup m p) (sub_ rd rs) -> 
  same_jump p (S p) ->
  v = minus (r rd) (r rs)  ->
  r' = updateR r rd v ->
  f' = updateF f ZF (beq_nat v 0) ->
  (p, r, f, m) ---> (S p, r', f', m)
  
| eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
  inst (lookup m p) (call rd) -> 
  p' = r rd ->
  valid_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (S (r' SP)) ->
  m'' = update m (r'' SP) (S p) ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
  inst (lookup m p)  ret ->
  p' = lookup m (r SP) ->
  valid_jump p p' ->
  set_stack p r m p' r' m' ->
  r'' = updateR r' SP (minus (r' SP) 1) ->
  (p, r, f, m) ---> (p', r'', f, m')
  
| eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (je ri) -> 
  f ZF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = true ->
  p' = r ri ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
  inst (lookup m p) (jl ri) -> 
  f SF = false ->
  p' = S p ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_jump : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
  inst (lookup m p) (jmp rd) -> 
  p' = r rd ->
  same_jump p p' ->
  (p, r, f, m) ---> (p', r, f, m)
  
| eval_halt : forall (p : Address) (r : RegisterFile) (f : Flags) (m : Memory),
  inst (lookup m p) halt ->
  (p, r, f, m) ---> (0, r, f, m)
  
  where "S '--->' S'" := (evalR S S') : type_scope.



Inductive do_n_steps: State -> nat -> State -> Prop :=
| do_0 : forall sta, do_n_steps sta 0 sta
| do_Sn : forall n sta sta' sta'', 
  sta ---> sta' ->
  do_n_steps sta' n sta'' ->
  do_n_steps sta (S n) sta''.

Definition anysteps (n : nat) (sta  : State) := 
  exists n' : nat , exists sta' : State,
      n' >= n /\ do_n_steps sta n' sta'.

Definition diverge (sta : State) := forall n, anysteps n sta.

