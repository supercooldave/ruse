Require Import MachineModel.


(* ===============================================================
   Labels for the trace semantics and the labelled operational
   ================================================================*)

Inductive Label := 
| Tau : Label
| Tick : Label
| Write_out : Address -> Value -> Label
| Call : RegisterFile -> Flags -> Address -> Label
| Callback : RegisterFile -> Flags -> Address -> Label
| Return : RegisterFile -> Flags -> Address -> Label
| Returnback : RegisterFile -> Flags -> Address -> Label.




