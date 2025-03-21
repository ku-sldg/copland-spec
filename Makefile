# Coq project makefile

# Documentation target.  Type "make DOC=all-gal.pdf" to make PDF.
DOC	?= gallinahtml

# File $(PROJ) contains the list of source files.
# See "man coq_makefile" for its format.
PROJ	= _CoqProject

# Generated makefile
COQMK	= coq.mk

TEMPLATE_REPO = https://github.com/Durbatuluk1701/coq-templates.git
SLDG_OPAM_REPO_PATH = https://github.com/ku-sldg/opam-repo.git
SLDG_OPAM_REPO_BRANCH = main
SLDG_OPAM_REPO_NAME = ku-sldg/opam-repo

COQBIN?=
ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

all:	
	dune build

test: all
	dune test

clean:
	dune clean

# Generates the meta files for the project
meta: 
	TMP=`mktemp -d` && \
	git clone $(TEMPLATE_REPO) $$TMP && \
	$$TMP/generate.sh

publish%:
	@echo "\nPublishing to $(SLDG_OPAM_REPO_NAME)\n\n\n"
	@echo "****************************************\nNOTE: Please make sure that the GITHUB TAGGED VERSION and the OPAM TAGGED VERSIONs are the same!\n****************************************\n\n\n"
	opam repo add -a $(SLDG_OPAM_REPO_NAME) $(SLDG_OPAM_REPO_PATH)
	opam publish --repo=$(SLDG_OPAM_REPO_NAME) --target-branch=$(SLDG_OPAM_REPO_BRANCH)

.PHONY:	all meta
