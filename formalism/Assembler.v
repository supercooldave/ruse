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
  starting_address : nat;
  code_size : nat;
  data_size : nat;
  no_entrypoints: nat
}.

Definition last_address (s : MemoryDescriptor) : Address :=
   starting_address s + code_size s + data_size s.


Inductive protected : MemoryDescriptor -> Address -> Prop :=
  Prot : forall (s : MemoryDescriptor) (p : Address), 
    starting_address s <= p -> p < last_address s -> protected s p.

Inductive unprotected : MemoryDescriptor -> Address -> Prop :=
  Unprot_before : forall (s : MemoryDescriptor) (p : Address), 
    p < starting_address s -> unprotected s p
| Unprot_after :  forall (s : MemoryDescriptor) (p : Address), 
  last_address s <= p -> unprotected s p.

Lemma protected_unprotected_disjoint :
  forall (s : MemoryDescriptor) (p : Address), not (protected s p /\ unprotected s p).
Proof.
  intros s p.
  intro.
  decompose [and] H.
  inversion H0.
  inversion H1 ; apply (lt_irrefl p); omega.
Qed.

Parameter entrypoint_size : nat.
Axiom non_zero_entrypoint_size : entrypoint_size > 0.


Definition entrypoint (s : MemoryDescriptor) (p : Address) : Prop :=
  exists (m : nat), m < no_entrypoints s /\ p = starting_address s + m * entrypoint_size.  

Definition data_segment (s : MemoryDescriptor) (p : Address) : Prop :=
  starting_address s + code_size s <= p /\ p < last_address s.

Definition return_entrypoint (s : MemoryDescriptor) (p : Address) : Prop :=
  p = starting_address s + no_entrypoints s * entrypoint_size.

Inductive read_allowed : MemoryDescriptor -> Address -> Address -> Prop :=
  read_protected : forall (s : MemoryDescriptor) (p a : Address),
    protected s p -> protected s a -> read_allowed s p a
| read_unprotected : forall (s : MemoryDescriptor) (p a : Address),
    unprotected s p -> unprotected s a -> read_allowed s p a.

Inductive write_allowed : MemoryDescriptor -> Address -> Address -> Prop :=
  write_protected : forall (s : MemoryDescriptor) (p a : Address),
    protected s p -> data_segment s a -> write_allowed s p a
| write_unprotected : forall (s : MemoryDescriptor) (p a : Address),
    unprotected s a -> write_allowed s p a.

Definition entry_jump (s : MemoryDescriptor) (p p' : Address) := 
  unprotected s p /\ entrypoint s p'.

Definition exit_jump (s : MemoryDescriptor) (p p' : Address) := 
  protected s p /\ unprotected s p'.

Definition int_jump (s : MemoryDescriptor) (p p' : Address) := 
  protected s p /\ protected s p' /\ ~ data_segment s p'.


Definition ext_jump (s : MemoryDescriptor) (p p' : Address) := 
  unprotected s p /\ unprotected s p'.

Definition same_jump  (s : MemoryDescriptor) (p p' : Address) := 
  int_jump s p p' \/ ext_jump s p p'.

Definition valid_jump  (s : MemoryDescriptor) (p p' : Address) := 
  same_jump s p p' \/ entry_jump s p p'  \/ exit_jump s p p'.


Definition SPsec (s : MemoryDescriptor) := starting_address s + code_size s.

Definition SPext (s : MemoryDescriptor) := last_address s.


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

Inductive set_stack : MemoryDescriptor -> Address -> RegisterFile -> Memory -> Address -> RegisterFile -> Memory -> Prop :=
  stack_out_to_in : forall (s : MemoryDescriptor) (p p' : Address) (m m': Memory) (r r': RegisterFile),
  entry_jump s p p' -> m' = store m (SPext s) (r SP) -> r' = updateR r SP (lookup m (SPsec s)) -> set_stack s p r m p' r' m'
| stack_in_to_out : forall (s : MemoryDescriptor) (p p' : Address) (m m' : Memory) (r r': RegisterFile),
  exit_jump s p p' -> m' = store m (SPsec s) (r SP) -> r' = updateR r SP (lookup m (SPext s)) -> set_stack s p r m p' r' m'
| stack_no_change : forall (s : MemoryDescriptor) (p p' : Address) (m : Memory) (r : RegisterFile),
  same_jump s p p' -> set_stack s p r m p' r m.

  

