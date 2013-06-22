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
  entry_points: nat
}.

Definition last_address (m : MemoryDescriptor) : Address :=
   starting_address m + code_size m + data_size m.


Inductive protected : MemoryDescriptor -> Address -> Prop :=
  Prot : forall (m : MemoryDescriptor) (p : Address), 
    starting_address m <= p -> p < last_address m -> protected m p.

Inductive unprotected : MemoryDescriptor -> Address -> Prop :=
  Unprot_before : forall (m : MemoryDescriptor) (p : Address), 
    p < starting_address m -> unprotected m p
| Unprot_after :  forall (m : MemoryDescriptor) (p : Address), 
  last_address m <= p -> unprotected m p.

Lemma protected_unprotected_disjoint :
  forall (m : MemoryDescriptor) (p : Address), not (protected m p /\ unprotected m p).
Proof.
  intros m p.
  intro.
  decompose [and] H.
  inversion H0.
  inversion H1 ; apply (lt_irrefl p); omega.
Qed.




  

  

