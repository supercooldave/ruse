Require Import Omega.

Inductive Register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11.

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


  

  

