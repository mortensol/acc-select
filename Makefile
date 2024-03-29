# -*- Makefile -*-

# --------------------------------------------------------------------
ECROOT   ?=
ECCHECK  ?=
ECARGS   ?= -no-eco
ECJOBS   ?= 2
ECCONF   := config/tests.config
XUNITOUT ?= xunit.yml
CHECKS   ?= select

ifeq ($(ECCHECK),)
ifeq ($(ECROOT),)
ECCHECK := ec-runtest
else
PATH    := ${ECROOT}:${PATH}
ECCHECK := $(ECROOT)/scripts/testing/runtest
endif
endif

# --------------------------------------------------------------------
.PHONY: default usage check check-xunit

default: check

usage:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --jobs=$(ECJOBS) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)

check-xunit:
	$(ECCHECK) --jobs=$(ECJOBS) --bin-args="$(ECARGS)" --report=$(XUNITOUT) $(ECCONF) $(CHECKS)
