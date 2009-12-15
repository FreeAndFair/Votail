# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.20 2005/07/20 17:34:08 wahlst Exp $

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

## ----------------------------------------------------------------- 
## At the bottom of this file we import $(TOPDIR)/Make.ProjDefs.  See the
## that file for substantial documentation.
## ----------------------------------------------------------------- 

TOPDIR =	../../../..

PACKAGE =	org.jmlspecs.models.tests

JAVAFILES =					\
		JMLObjectSequenceTest		\
		JMLObjectBagTest		\
		JMLObjectSetTest		\

TESTFILES = $(JAVAFILES)

## -------------------------------------------------------------
## Goals

build-this:	classes

runtests-this: TestSuite.out

## -------------------------------------------------------------
## Testing

JAVAFLAGS = -O -g

all: compile

check: checkallspecs compile

# check all JML specs.
checkallspecs:
	$(JML) $(JMLFLAGS) . 2>&1 | tee checkallspecs.out-ckd

checked-tests: 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

compile:	classes

# Clean up stuff
#
clean-this : cleanlocal

cleanlocal:
	$(RM) *.*-ckd core

clean-classes-this: remove-dot-class-files

## -------------------------------------------------------------
## Global defaults

include $(TOPDIR)/Make.ProjDefs

#%.out: %.class
#	$(JUNITFORJML) $(PACKAGE).$* 2>&1 | tee $*.out

#TestSuite.out: $(addsuffix .class,$(TESTFILES)) TestSuite.class 
.PHONY: TestSuite.out
TestSuite.out: 
	@$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

JUNITFORJML = $(JAVAFORJML) junit.textui.TestRunner
