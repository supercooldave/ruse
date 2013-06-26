
(* This serves as an intermediate data structure between a trace from the 
   trace semantics and the code that implements the context capable of
   producing the trace. *)

(* First note that any trace is well-bracketed, or can be made to be so, 
   which means that each call has a corresponding return and calls and returns
   are properly nested. *)

(* The proof of soundness, namely two guys are not trace equivalent means that 
   are not contextually equivalent, requires that a context be produced for
   a given pair of traces. A simpler approach is to start with a single trace
   and try to find a context that produces it. *)

(* The first step is to produce an element of the corresponding data structure
   for the given trace. The data structure includes the following information:
   - the target of the call etc
   - the step number
   - the sequencing of instructions (abstracting what occurs in a method)
   - the bracketing
*)

(* Second step is to take the produced element of the data structure and use
   it as the basis for generating code. The theorem then is that the generated
   code produces the trace encoded in the data structure -- and also that
   the data structure encodes the trace. *)

(* The idea is that the separation makes it easier to manage the production of
   code corresponding to the context. And that the additional structure inferred
   can help with the proof and construction of code. *)
