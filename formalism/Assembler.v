Require Import Omega.

Inductive Register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | SP.
Inductive Flag := SF | ZF.
Inductive Bit := O | I.

Definition Address := nat.
Definition Value := nat.

Inductive Instruction :=
   movl : Register -> Register -> Instruction
 | movs : Register -> Register -> Instruction
 | movi : Register -> Value    -> Instruction
 | add  : Register -> Register -> Instruction
 | sub  : Register -> Register -> Instruction
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

Open Scope type_scope.
Definition State := Memory * RegisterFile * Flags.
Close Scope type_scope.

Inductive set_stack : Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump p p' -> m' = store m SPext (r SP) -> r' = updateR r SP (lookup m SPsec) -> set_stack p r m p' r' m'
| stack_in_to_out : forall (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump p p' -> m' = store m SPsec (r SP) -> r' = updateR r SP (lookup m SPext) -> set_stack p r m p' r' m'
| stack_no_change : forall (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump p p' -> set_stack p r m p' r m.

  

