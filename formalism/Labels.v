Require Import MachineModel.


(* ===============================================================
   Labels for the trace semantics and the labelled operational
   ================================================================*)

Inductive Label := 
| Tau : Label
| Tick : Label
| Write_out : Address -> Value -> Label
| Call : RegisterFile -> Flags -> Value -> Label
| Callback : RegisterFile -> Flags -> Value -> Label
| Return : RegisterFile -> Flags -> Value -> Label
| Returnback : RegisterFile -> Flags -> Value -> Label.




