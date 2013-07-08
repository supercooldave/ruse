# Ruse formalism project makefile.
# Dave Clarke, Marco Patrignani 2013.

# The modules to be compiled by default.  
# For these, just call “make” at the commandline.

default: Assembler MachineModel SameJumpTransitions Labels OperationalSemantics LabelledOperationalSemantics TraceSemantics ResultsLab Results TraceTree


# All modules (invoked by “make all”).
all: Assembler MachineModel SameJumpTransitions Labels OperationalSemantics LabelledOperationalSemantics TraceSemantics ResultsLab Results TraceTree

# Command to be used for compiling coq files.
# Change this locally if eg “hoqc” doesn’t resolve correctly on your system.
COQC=coqc

## FIX dependencies

# Specific files involved in each submodule: 
Assembler: MachineModel
	$(COQC) Assembler.v

MachineModel: 
	$(COQC) MachineModel.v

OperationalSemantics: MachineModel
	$(COQC) OperationalSemantics.v

LabelledOperationalSemantics: OperationalSemantics Labels
	$(COQC) LabelledOperationalSemantics.v

TraceTree: Labels Assembler
	$(COQC) TraceTree.v 

TraceSemantics: Labels
	$(COQC) TraceSemantics.v

Labels: Assembler
	$(COQC) Labels.v

Results: 
	$(COQC) Results.v

ResultsLab:	
	$(COQC) ResultsLab.v

SameJumpTransitions:
	$(COQC) SameJumpTransitions.v	

# Call “make clean” to remove all compiled files:
clean:
	rm -rf *.vo *.glob