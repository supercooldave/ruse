# Ruse formalism project makefile.
# Dave Clarke, Marco Patrignani 2013.

# The modules to be compiled by default.  
# For these, just call “make” at the commandline.

default: Assembler OperationalSemantics TraceTree LabelledOperationalSemantics MachineModel 
# TraceSemantics Results

# All modules (invoked by “make all”).
all: Assembler OperationalSemantics TraceTree LabelledOperationalSemantics  MachineModel 
# TraceSemantics Results

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

LabelledOperationalSemantics: OperationalSemantics
	$(COQC) LabelledOperationalSemantics.v

TraceTree: 
	$(COQC) TraceTree.v

# Call “make clean” to remove all compiled files:
clean:
	rm -rf *.vo *.glob