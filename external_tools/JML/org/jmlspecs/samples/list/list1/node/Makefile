# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.4 2004/07/14 02:32:39 cruby Exp $

# Copyright (C) 1998, 1999 Iowa State University

# This file is part of JML

# JML is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.

# JML is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with JML; see the file COPYING.  If not, write to
# the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

#
# Developer's Makefile for testing JML specs
#

PACKAGE = org.jmlspecs.samples.list.list1.node

JAVAFILES = \
		SLNode \
		DLNode 

NAMESTOTEST = SLNode DLNode 

JML_REFINED_FILES = $(addsuffix .jml-refined, $(JAVAFILES))
JML_FILES = $(addsuffix .jml, $(JAVAFILES))
JAVA_FILES = $(addsuffix .java, $(JAVAFILES))

TOPDIR = ../../../../../..

RAC_CLASSES_DIR = $(TOPDIR)/raccompiled/$(subst .,/,$(PACKAGE))

TESTFILES = $(addsuffix _JML_Test,$(NAMESTOTEST))
TESTRUNFILES = $(addsuffix _JML_Test.java,$(NAMESTOTEST))

GENFILES = $(TESTRUNFILES)

default all: check

buildtests-this-before: $(TESTRUNFILES)

%_JML_Test.java: %.java
	$(JMLUNIT) $(JMLUNITFLAGS) $?

TestSuite.out: $(RAC_CLASSES_DIR)/raccompile.stamp \
		$(JML_REFINED_FILES) $(JML_FILES) $(JAVA_FILES) \
		$(TESTRUNFILES)  TestSuite.class 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

TestSuite.dout: $(NONFRAC_CLASSES_DIR)/raccompile.stamp \
		$(TESTRUNFILES) TestSuite.class 
	env CLASSPATH="$(NONFRAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.dout
	@grep -q 'FAILURES!!!' TestSuite.dout && exit 1 || exit 0

.PHONY: check
check: checkallspecs compile

# check all JML specs.
.PHONY: checkallspecs
checkallspecs: $(TESTRUNFILES)
	$(JML) $(JMLFLAGS) .

runtests-this: runtests-local

.PHONY: runtests-local
runtests-local: $(TESTRUNFILES)
	@if test -f skip; \
	  then \
	    for f in *.java ; \
	    do \
		grep -q $${f} skip || $(JML) $(JMLFLAGS) $${f} ; \
	    done; \
	  else \
	       $(JML) $(JMLFLAGS) . ; \
	  fi

compile-this: compile-local

.PHONY: compile-local
compile-local: $(TESTRUNFILES)
	$(JAVAC) $(JAVAFLAGS) *.java

# Clean up stuff
clean-this : cleanlocal

.PHONY: cleanlocal
cleanlocal: 
	$(RM) *.*-ckd core *.out

include $(TOPDIR)/Make.ProjDefs
