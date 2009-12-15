# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.6 2004/10/05 04:53:50 leavens Exp $

# Copyright (C) 2003 Iowa State University

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

TOPDIR = ../../..

SUBDIRS = 

PACKAGE = org.jmlspecs.lang

RAC_CLASSES_DIR = $(TOPDIR)/raccompiled/$(subst .,/,$(PACKAGE))
NONFRAC_CLASSES_DIR = $(TOPDIR)/nonFraccompiled/$(subst .,/,$(PACKAGE))

# JAVAFLAGS = -g -J-mx256m
JAVAFLAGS = -O -J-mx256m

# JAVADOCFLAGS =
JAVADOC = javadoc
JAVADOCDIR = ../../../javadocs
JAVADOCFLAGS =  \
		-d $(JAVADOCDIR) \
		-doctitle "JML Language" \
		-windowtitle "JML Language" \
		-header "<H1>JML Language</H1>"

ALL_JAVA = 	JMLDataGroup.java


# set JAVAFILES for Make.Defs
JAVAFILES = $(subst .java,,$(ALL_JAVA))

# Don't set set TESTDIRS, TESTSUITES, TESTFILES for Make.Defs
# as we don't want to build TestSuite.java for this directory
#TESTDIRS = 
#TESTSUITES = 

NAMESTOTEST = $(JAVAFILES)

#TESTFILES = $(addsuffix _JML_Test,$(NAMESTOTEST))
TESTDATACLASSFILES = $(addsuffix _JML_TestData.class,$(NAMESTOTEST))

GENFILES = $(addsuffix .java,$(TESTFILES))

## -------------------------------------------------------------
## Goals

default all: check html

## -------------------------------------------------------------
## building

compile: build

## -------------------------------------------------------------
## Testing

check: runtests-this-start checkallspecs runtests-this-end

buildtests-this-before: java.stamp

java.stamp: $(addsuffix .java,$(NAMESTOTEST))
	$(JMLUNIT) $(JMLUNITFLAGS) $?
	touch java.stamp

slowtests: 
	 $(MAKE) JMLCFLAGS= build buildtests TestSuite.out

fasterslowtests: TestSuite.out

individual-tests: $(addsuffix .out, $(NAMESTOTEST))

TestSuite.out: $(RAC_CLASSES_DIR)/raccompile.stamp \
		java.stamp $(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

TestSuite.dout: $(NONFRAC_CLASSES_DIR)/raccompile.stamp \
		java.stamp $(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(NONFRAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.dout
	@grep -q 'FAILURES!!!' TestSuite.dout && exit 1 || exit 0

runtests-this: checkallspecs

ifdef ALLTESTS
runtests-this: JMLDataGroup.out
endif

# check all JML specs.
checkallspecs: java.stamp
	@if [ $(QUIET) ]; then echo "."; else echo "running checker on specs"; fi;
	@if $(JML) $(JMLFLAGS) . > checkallspecs.out-ckd 2>&1 ; \
	then cat checkallspecs.out-ckd ; \
	else cat checkallspecs.out-ckd ; exit 1 ; \
	fi

escjava: 
	$(ESCJAVA) $(ESCJAVAFLAGS) $(ALL_JAVA)

## docs
docs html: packages.html

packages.html: $(ALL_GENERATED_JAVA)
	mkdir -p $(JAVADOCDIR) 
	$(JAVADOC) $(JAVADOCFLAGS) *.java > /tmp/tempjavadoc
	$(JMLDOC) -Q -package *.java


# Clean up stuff
#
clean-this:	cleanlocal

cleanlocal: 
	$(RM) *.*-ckd core *.out java.stamp

distclean-this:	distclean-local

distclean-local:
	$(RM) stylesheet.css package-list
	$(RM) -r org

distclean-javadocs:
	$(RM) -r $(JAVADOCDIR)/org/jmlspecs/models

## -------------------------------------------------------------
## Global defaults

include $(TOPDIR)/Make.ProjDefs
