# Simplified Windows-compatible Makefile for Coq project
# Project: Checkpointing-with-Static-Analysis

# Configuration from _CoqProject
COQFLAGS := -R coq Spyte
COQC := coqc
COQDEP := coqdep
COQBIN :=

# Source directory and files
SRC_DIR := coq
VFILES := $(wildcard $(SRC_DIR)\*.v)
VOFILES := \
	coq\Bytecode.vo \
	coq\Python.vo \
	coq\Tac.vo \
	coq\Lower.vo \
	coq\TypeCore.vo \
	coq\TypeSig.vo \
	coq\Pointer.vo \
	coq\TypeLattice.vo \
	coq\TypeOps.vo \
	coq\TypeUnify.vo \
	coq\TypeSystem.vo \
	coq\Main.vo

VDFILE := .Makefile.d

# Default target
all: $(VOFILES)
.PHONY: all

# Dependency generation
$(VDFILE): $(VFILES)
	@echo COQDEP VFILES
	@$(COQDEP) $(COQFLAGS) $(VFILES) > $(VDFILE) || (del $(VDFILE) && exit 1)

# Include dependencies
-include $(VDFILE)

# Compilation rule for .v to .vo
$(VOFILES): %.vo: %.v | $(VDFILE)
	@echo COQC $<
	@$(COQC) $(COQFLAGS) $<

# Clean target
clean:
	@echo CLEAN
	@del $(SRC_DIR)\*.vo $(SRC_DIR)\*.vos $(SRC_DIR)\*.vok $(SRC_DIR)\*.glob $(SRC_DIR)\*.aux $(VDFILE)
.PHONY: clean

# Ensure COQBIN is set if needed
COQC := $(if $(COQBIN),$(COQBIN)coqc,$(COQC))
COQDEP := $(if $(COQBIN),$(COQBIN)coqdep,$(COQDEP))
