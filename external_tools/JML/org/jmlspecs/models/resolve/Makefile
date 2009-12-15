# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.34 2004/02/07 22:30:58 leavens Exp $

# Copyright (C) 1998-2002 Iowa State University

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

PACKAGE =	org.jmlspecs.models.resolve

RAC_CLASSES_DIR = $(TOPDIR)/raccompiled/$(subst .,/,$(PACKAGE))
NONFRAC_CLASSES_DIR = $(TOPDIR)/nonFraccompiled/$(subst .,/,$(PACKAGE))

ESCJAVA = escjava -quiet

# JAVAFILES SET BELOW

JAVASRCONLY = \
	AntisymmetricCompareTo \
	AsymmetricCompareTo \
	CompareTo \
	DenselyOrderedCompareTo \
	PartiallyOrderedCompareTo \
	PreorderedCompareTo \
	ReflexiveCompareTo \
	StrictPartiallyOrderedCompareTo \
	StrictlyOrderedCompareTo \
	SymmetricCompareTo \
	TotalCompareTo \
	TotalPreorderedCompareTo \
	TotallyOrderedCompareTo \
	TransitiveCompareTo \
	TrichotomousCompareTo \
	UndefinedException

NAMESTOTEST = \
	NaturalNumber \
	StringOfObject

JAVAFILES =  $(JAVASRCONLY) $(NAMESTOTEST)

TESTFILES = $(addsuffix _JML_Test,$(NAMESTOTEST))
TESTDATACLASSFILES = $(addsuffix _JML_TestData.class,$(NAMESTOTEST))

GENFILES = $(addsuffix .java,$(TESTFILES))

## -------------------------------------------------------------
## Goals

default all: check

## -------------------------------------------------------------
## building

compile: build

## -------------------------------------------------------------
## Testing

check: checkallspecs build buildtests

buildtests-this-before: java.stamp

java.stamp: $(addsuffix .java,$(NAMESTOTEST))
	$(JMLUNIT) $(JMLUNITFLAGS) $?
	touch java.stamp

slowtests:
	 $(MAKE) JMLCFLAGS= TestSuite.dout

fasterslowtests: TestSuite.out

TestSuite.out: $(RAC_CLASSES_DIR)/raccompile.stamp \
		$(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

TestSuite.dout: $(NONFRAC_CLASSES_DIR)/raccompile.stamp \
		$(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(NONFRAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.dout
	@grep -q 'FAILURES!!!' TestSuite.dout && exit 1 || exit 0

runtests-this: checkallspecs

# check all JML specs.
checkallspecs:
	@if [ $(QUIET) ]; then echo "."; else echo "running checker on specs"; fi;
	@if $(JML) $(JMLFLAGS) . > checkallspecs.out-ckd 2>&1 ; \
	then cat checkallspecs.out-ckd ; \
	else cat checkallspecs.out-ckd ; exit 1 ; \
	fi

escjava: 
	$(ESCJAVA) $(ESCJAVAFLAGS) $(addsuffix .java,$(JAVAFILES))


# Clean up stuff
#
clean-this:	cleanlocal

cleanlocal: 
	$(RM) *.*-ckd core *.out

distclean-this:	distclean-local

distclean-local:
	$(RM) -r org $(JAVADOCDIR)/org/jmlspecs/models/resolve

## -------------------------------------------------------------
## Global defaults

include $(TOPDIR)/Make.ProjDefs
