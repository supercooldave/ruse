Require Import Omega.

Inductive Register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | SP.
Inductive Flag := SF | ZF.
Definition Bit := bool. 

(* TODO: Find better home for these -- better still, see if they are in Coq lib. *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  if andb (ble_nat n m) (negb (beq_nat n m)) then true else false.

Definition Address := nat.
Definition Value := nat.

Inductive Instruction :=
   movl : Register -> Register -> Instruction
 | movs : Register -> Register -> Instruction
 | movi : Register -> Value    -> Instruction
 | add_ : Register -> Register -> Instruction
 | sub_ : Register -> Register -> Instruction
 | cmp  : Register -> Register -> Instruction
 | jmp  : Register             -> Instruction
 | je   : Register             -> Instruction
 | jl   : Register             -> Instruction
 | call : Register             -> Instruction
 | ret  :                         Instruction
 | halt :                         Instruction.

Record MemoryDescriptor := MemDesc {
  starting_address_ : nat;
  code_size_ : nat;
  data_size_ : nat;
  no_entrypoints_ : nat
}.

Parameter s : MemoryDescriptor.

Definition starting_address := starting_address_ s.
Definition code_size := code_size_ s.
Definition data_size := data_size_ s.
Definition no_entrypoints := no_entrypoints_ s.

Definition last_address : Address := starting_address + code_size + data_size.


Inductive protected :Address -> Prop :=
  Prot : forall (p : Address), starting_address <= p -> p < last_address -> protected p.

Inductive unprotected :Address -> Prop :=
  Unprot_before : forall (p : Address), p < starting_address -> unprotected p
| Unprot_after :  forall (p : Address), last_address <= p -> unprotected p.

Lemma protected_unprotected_disjoint :
  forall (p : Address), not (protected p /\ unprotected p).
Proof.
  intros p H.
  decompose [and] H.
  inversion H0.
  inversion H1 ; apply (lt_irrefl p); omega.
Qed.

Parameter entrypoint_size : nat.
Axiom non_zero_entrypoint_size : entrypoint_size > 0.

Definition entrypoint (p : Address) : Prop :=
  exists (m : nat), m < no_entrypoints /\ p = starting_address + m * entrypoint_size.  

Definition data_segment (p : Address) : Prop :=
  starting_address + code_size <= p /\ p < last_address.

Definition return_entrypoint (p : Address) : Prop :=
  p = starting_address + no_entrypoints * entrypoint_size.

Inductive read_allowed : Address -> Address -> Prop :=
  read_protected : forall (p a : Address), protected p -> protected a -> read_allowed p a
| read_unprotected : forall (p a : Address), unprotected p -> unprotected a -> read_allowed p a.

Inductive write_allowed : Address -> Address -> Prop :=
  write_protected : forall (p a : Address), protected p -> data_segment a -> write_allowed p a
| write_unprotected : forall (p a : Address), unprotected a -> write_allowed p a.

Definition entry_jump (p p' : Address) := unprotected p /\ entrypoint p'.

Definition exit_jump (p p' : Address) := protected p /\ unprotected p'.

Definition int_jump (p p' : Address) := protected p /\ protected p' /\ ~ data_segment p'.

Definition ext_jump (p p' : Address) := unprotected p /\ unprotected p'.

Definition same_jump (p p' : Address) := int_jump p p' \/ ext_jump p p'.

Definition valid_jump (p p' : Address) := same_jump p p' \/ entry_jump p p'  \/ exit_jump p p'.


Definition SPsec := starting_address  + code_size.

Definition SPext := last_address.


Parameter Memory : Set.
Parameter lookup : Memory -> Address -> Value.
Parameter store : Memory -> Address -> Value -> Memory.

Definition RegisterFile := Register -> nat.
(*
Definition updateR (r : RegisterFile) (reg : Register) (v : Value) : RegisterFile :=
  fun (reg' : Register) => if (reg = reg') then v else r reg.
*)
Parameter updateR : RegisterFile -> Register -> Value -> RegisterFile.

Definition Flags := Flag -> Bit. 
Parameter updateF : Flags -> Flag -> Bit -> Flags.

Inductive set_stack : Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump p p' -> m' = store m SPext (r SP) -> r' = updateR r SP (lookup m SPsec) -> set_stack p r m p' r' m'
| stack_in_to_out : forall (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump p p' -> m' = store m SPsec (r SP) -> r' = updateR r SP (lookup m SPext) -> set_stack p r m p' r' m'
| stack_no_change : forall (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump p p' -> set_stack p r m p' r m.

  
Open Scope type_scope.
Definition State := Address * RegisterFile * Flags * Memory.
Close Scope type_scope.

Reserved Notation "S '--->' S'" (at level 50, left associativity).

Parameter inst : Memory -> Address -> Instruction -> Prop.
(* TODO : Some axiom stating that each decoded value is unique. *)

Inductive evalR : State -> State -> Prop :=
  eval_movl : forall (p : Address) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd rs : Register),
    inst m p (movl rd rs) -> 
    valid_jump p (S p) ->
    read_allowed p (lookup m (r rs)) -> 
    r' = updateR r rd (lookup m (r rs)) ->  
    (p, r, f, m) ---> (S p, r', f, m)

| eval_movs : forall (p : Address) (r : RegisterFile) (f : Flags) (m m' : Memory) (rd rs : Register),
    inst m p (movs rd rs) -> 
    valid_jump p (S p) ->
    write_allowed p (lookup m (r rd)) -> 
    m' = store m (lookup m (r rs)) (r rd) ->  
    (p, r, f, m) ---> (S p, r, f, m')

| eval_movi : forall (p : Address) (i : Value) (r r' : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
    inst m p (movi rd i) -> 
    valid_jump p (S p) ->
    r' = updateR r rd i ->  
    (p, r, f, m) ---> (S p, r', f, m)

| eval_compare : forall (p : Address) (r : RegisterFile) (f f' : Flags) (m : Memory) (r1 r2 : Register),
    inst m p (cmp r1 r2) -> 
    valid_jump p (S p) ->
    f' = updateF (updateF f ZF (beq_nat (r r1) (r r2))) SF (blt_nat (r r1) (r r2)) ->
    (p, r, f, m) ---> (S p, r, f', m)

| eval_add : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
    inst m p (add_ rd rs) -> 
    valid_jump p (S p) ->
    v = plus (r rd) (r rs)  ->
    r' = updateR r rd v ->
    f' = updateF f ZF (beq_nat v 0) ->
    (p, r, f, m) ---> (S p, r', f', m)

| eval_sub : forall (p : Address) (r r' : RegisterFile) (f f' : Flags) (v : Value) (m : Memory) (rd rs : Register),
    inst m p (sub_ rd rs) -> 
    valid_jump p (S p) ->
    v = minus (r rd) (r rs)  ->
    r' = updateR r rd v ->
    f' = updateF f ZF (beq_nat v 0) ->
    (p, r, f, m) ---> (S p, r', f', m)

(* TODO: Add other instructions *)

| eval_call : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' m'' : Memory) (rd : Register),
    inst m p (call rd) -> 
    p' = r rd ->
    valid_jump p p' ->
    set_stack p r m p' r' m' ->
    r'' = updateR r' SP (S (r' SP)) ->
    m'' = store m (r'' SP) (S p) ->
    (p, r, f, m) ---> (p', r, f, m)

| eval_ret : forall (p p' : Address) (r r' r'' : RegisterFile) (f : Flags) (m m' : Memory),
    inst m p ret ->
    p' = lookup m (r SP) ->
    valid_jump p p' ->
    set_stack p r m p' r' m' ->
    r'' = updateR r' SP (minus (r' SP) 1) ->
    (p, r, f, m) ---> (p', r'', f, m')

| eval_je_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
    inst m p (je ri) -> 
    f ZF = true ->
    p' = r ri ->
    same_jump p p' ->
    (p, r, f, m) ---> (p', r, f, m)

| eval_je_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
    inst m p (je ri) -> 
    f ZF = false ->
    p' = S p ->
    same_jump p p' ->
    (p, r, f, m) ---> (p', r, f, m)

| eval_jl_true : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
    inst m p (jl ri) -> 
    f SF = true ->
    p' = r ri ->
    same_jump p p' ->
    (p, r, f, m) ---> (p', r, f, m)

| eval_jl_false : forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (ri : Register),
    inst m p (jl ri) -> 
    f SF = false ->
    p' = S p ->
    same_jump p p' ->
    (p, r, f, m) ---> (p', r, f, m)

| eval_jump :  forall (p p' : Address) (r : RegisterFile) (f : Flags) (m : Memory) (rd : Register),
    inst m p (jmp rd) -> 
    p' = r rd ->
    same_jump p p' ->
    (p, r, f, m) ---> (p', r, f, m)

(*
| eval_halt  -- how to deal with -1?
*)

where "S '--->' S'" := (evalR S S') : type_scope.
