# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.88 2004/06/01 19:51:43 leavens Exp $

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

TOPDIR = ../../..

SUBDIRS = tests resolve

PACKAGE = org.jmlspecs.models

RAC_CLASSES_DIR = $(TOPDIR)/raccompiled/$(subst .,/,$(PACKAGE))
NONFRAC_CLASSES_DIR = $(TOPDIR)/nonFraccompiled/$(subst .,/,$(PACKAGE))

# JAVAFLAGS = -g -J-mx256m
JAVAFLAGS = -O -J-mx256m

# JAVADOCFLAGS =
JAVADOC = javadoc
JAVADOCDIR = ../../../javadocs
JAVADOCFLAGS =  \
		-d $(JAVADOCDIR) \
		-doctitle "JML Models" \
		-windowtitle "JML Models" \
		-header "<H1>JML Models</H1>"

JAVA_LISTS = JMLListValueNode.java \
		JMLListEqualsNode.java \
		JMLListObjectNode.java
JAVA_SETS = JMLValueSet.java \
		JMLEqualsSet.java \
		JMLObjectSet.java \
		JMLValueSetEnumerator.java \
		JMLEqualsSetEnumerator.java \
		JMLObjectSetEnumerator.java
JAVA_SEQUENCES = JMLValueSequence.java \
		JMLEqualsSequence.java \
		JMLObjectSequence.java \
		JMLValueSequenceEnumerator.java \
		JMLEqualsSequenceEnumerator.java \
		JMLObjectSequenceEnumerator.java
JAVA_BAGS = JMLValueBag.java \
		JMLEqualsBag.java \
		JMLObjectBag.java \
		JMLValueBagEnumerator.java \
		JMLEqualsBagEnumerator.java \
		JMLObjectBagEnumerator.java
JAVA_PAIRS = JMLValueValuePair.java \
		JMLValueEqualsPair.java \
		JMLValueObjectPair.java \
		JMLEqualsValuePair.java \
		JMLEqualsEqualsPair.java \
		JMLEqualsObjectPair.java \
		JMLObjectValuePair.java \
		JMLObjectEqualsPair.java \
		JMLObjectObjectPair.java
JAVA_RELATIONS = JMLValueToValueRelation.java \
		JMLValueToEqualsRelation.java \
		JMLValueToObjectRelation.java \
		JMLEqualsToValueRelation.java \
		JMLEqualsToEqualsRelation.java \
		JMLEqualsToObjectRelation.java \
		JMLObjectToValueRelation.java \
		JMLObjectToEqualsRelation.java \
		JMLObjectToObjectRelation.java
JAVA_MAPS = JMLValueToValueMap.java \
		JMLValueToEqualsMap.java \
		JMLValueToObjectMap.java \
		JMLEqualsToValueMap.java \
		JMLEqualsToEqualsMap.java \
		JMLEqualsToObjectMap.java \
		JMLObjectToValueMap.java \
		JMLObjectToEqualsMap.java \
		JMLObjectToObjectMap.java
JAVA_REL_ENUMS = JMLValueToValueRelationEnumerator.java \
		JMLValueToEqualsRelationEnumerator.java \
		JMLValueToObjectRelationEnumerator.java \
		JMLEqualsToValueRelationEnumerator.java \
		JMLEqualsToEqualsRelationEnumerator.java \
		JMLEqualsToObjectRelationEnumerator.java \
		JMLObjectToValueRelationEnumerator.java \
		JMLObjectToEqualsRelationEnumerator.java \
		JMLObjectToObjectRelationEnumerator.java
JAVA_REL_IMAGE_ENUMS = JMLValueToValueRelationImageEnumerator.java \
		JMLValueToEqualsRelationImageEnumerator.java \
		JMLValueToObjectRelationImageEnumerator.java \
		JMLEqualsToValueRelationImageEnumerator.java \
		JMLEqualsToEqualsRelationImageEnumerator.java \
		JMLEqualsToObjectRelationImageEnumerator.java \
		JMLObjectToValueRelationImageEnumerator.java \
		JMLObjectToEqualsRelationImageEnumerator.java \
		JMLObjectToObjectRelationImageEnumerator.java
ALL_GENERATED_JAVA = $(JAVA_LISTS) $(JAVA_SETS) $(JAVA_SEQUENCES) \
		$(JAVA_BAGS) $(JAVA_PAIRS) \
		$(JAVA_RELATIONS) $(JAVA_MAPS) $(JAVA_REL_ENUMS) \
		$(JAVA_REL_IMAGE_ENUMS)

ALL_JAVA = $(ALL_GENERATED_JAVA) \
		JMLArrayOps.java \
		JMLByte.java \
		JMLChar.java \
		JMLComparable.java \
		JMLDouble.java \
		JMLFiniteInteger.java \
		JMLFloat.java \
		JMLInfiniteInteger.java \
		JMLInfiniteIntegerClass.java \
		JMLInteger.java \
		JMLListException.java \
		JMLLong.java \
		JMLMapException.java \
		JMLModelValueSet.java \
		JMLNegativeInfinity.java \
		JMLNoSuchElementException.java \
		JMLNullSafe.java \
		JMLObjectType.java \
		JMLPositiveInfinity.java \
		JMLResources.java \
		JMLSequenceException.java \
		JMLShort.java \
		JMLString.java \
		JMLType.java \
		JMLTypeException.java \
		JMLValueSequenceSpecs.java \
		JMLValueSetSpecs.java \
		JMLValueBagSpecs.java \
		JMLValueType.java \
		JMLIterator.java \
		JMLEnumeration.java \
		JMLEnumerationToIterator.java \
		JMLCollection.java


# set JAVAFILES for Make.Defs
JAVAFILES = $(subst .java,,$(ALL_JAVA))

# set TESTDIRS, TESTSUITES, TESTFILES for Make.Defs
TESTDIRS = tests resolve
TESTSUITES = tests resolve

NAMESTOTEST = JMLChar \
		JMLFloat \
		JMLInfiniteInteger \
		JMLInteger \
		JMLNullSafe \
		JMLString \
		JMLValueSet \
		JMLObjectToObjectRelation \
		JMLListValueNode \
		JMLValueToValueMap \
		JMLValueObjectPair

TESTFILES = $(addsuffix _JML_Test,$(NAMESTOTEST))
TESTDATACLASSFILES = $(addsuffix _JML_TestData.class,$(NAMESTOTEST))

GENFILES = $(addsuffix .java,$(TESTFILES))

## -------------------------------------------------------------
## Goals

default all: check html

## -------------------------------------------------------------
## building

compile: build

build-this-before: generate

generate: $(ALL_GENERATED_JAVA)

$(JAVA_MODEL_SETS): JMLModelSet.java-generic JMLModelSet.sh
	$(RM) $(JAVA_MODEL_SETS)
	sh JMLModelSet.sh all java
	chmod a-w $(JAVA_MODEL_SETS)

$(JAVA_LISTS): JMLListNode.java-generic JMLListNode.sh
	$(RM) $(JAVA_LISTS)
	sh JMLListNode.sh all java
	chmod a-w $(JAVA_LISTS)

$(JAVA_SETS): JMLSet.java-generic JMLSet.sh JMLSetEnumerator.java-generic
	$(RM) $(JAVA_SETS)
	sh JMLSet.sh all java
	chmod a-w $(JAVA_SETS)

$(JAVA_SEQUENCES): JMLSequence.java-generic JMLSequence.sh \
		 JMLSequenceEnumerator.java-generic
	$(RM) $(JAVA_SEQUENCES)
	sh JMLSequence.sh all java
	chmod a-w $(JAVA_SEQUENCES)

$(JAVA_BAGS): JMLBag.java-generic JMLBag.sh JMLBagEnumerator.java-generic
	$(RM) $(JAVA_BAGS)
	sh JMLBag.sh all java
	chmod a-w $(JAVA_BAGS)

$(JAVA_PAIRS): JMLPair.java-generic JMLPair.sh 
	$(RM) $(JAVA_PAIRS)
	sh JMLPair.sh all all
	chmod a-w $(JAVA_PAIRS)

$(JAVA_RELATIONS): JMLRelation.java-generic JMLRelation.sh 
	$(RM) $(JAVA_RELATIONS)
	sh JMLRelation.sh Relation all all
	chmod a-w $(JAVA_RELATIONS)

$(JAVA_REL_ENUMS): JMLRelationEnumerator.java-generic JMLRelation.sh 
	$(RM) $(JAVA_REL_ENUMS)
	sh JMLRelation.sh RelationEnumerator all all
	chmod a-w $(JAVA_REL_ENUMS)

$(JAVA_REL_IMAGE_ENUMS): JMLRelationImageEnumerator.java-generic \
			JMLRelation.sh 
	$(RM) $(JAVA_REL_IMAGE_ENUMS)
	sh JMLRelation.sh RelationImageEnumerator all all
	chmod a-w $(JAVA_REL_IMAGE_ENUMS)

$(JAVA_MAPS): JMLMap.java-generic JMLMap.sh
	$(RM) $(JAVA_MAPS)
	sh JMLMap.sh all all
	chmod a-w $(JAVA_MAPS)

## -------------------------------------------------------------
## Testing

check: runtests-this-start checkallspecs runtests-this-end

buildtests-this-before: generate java.stamp

java.stamp: $(addsuffix .java,$(NAMESTOTEST))
	$(JMLUNIT) $(JMLUNITFLAGS) $?
	touch java.stamp

slowtests: 
	 $(MAKE) JMLCFLAGS= build buildtests TestSuite.dout

fasterslowtests: TestSuite.out

individual-static-tests individual-tests: $(addsuffix .out, $(NAMESTOTEST))

individual-dynamic-tests: $(addsuffix .dout, $(NAMESTOTEST))

TestSuite.out: $(RAC_CLASSES_DIR)/raccompile.stamp \
		$(RAC_CLASSES_DIR)/resolve/raccompile.stamp \
		java.stamp $(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

$(RAC_CLASSES_DIR)/resolve/raccompile.stamp:
	$(MAKE) -C resolve raccompile-static

TestSuite.dout: $(NONFRAC_CLASSES_DIR)/raccompile.stamp \
		$(NONFRAC_CLASSES_DIR)/resolve/raccompile.stamp \
		java.stamp $(TESTDATACLASSFILES) TestSuite.class 
	env CLASSPATH="$(NONFRAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.dout
	@grep -q 'FAILURES!!!' TestSuite.dout && exit 1 || exit 0

$(NONFRAC_CLASSES_DIR)/resolve/raccompile.stamp: 
	$(MAKE) -C resolve raccompile-dynamic

runtests-this: checkallspecs

ifdef ALLTESTS
runtests-this: TestSuite.out
endif

# check all JML specs.
checkallspecs: $(ALL_GENERATED_JAVA) java.stamp
	@if [ $(QUIET) ]; then echo "."; else echo "running checker on specs"; fi;
	@if $(JML) $(JMLFLAGS) . > checkallspecs.out-ckd 2>&1 ; \
	then cat checkallspecs.out-ckd ; \
	else cat checkallspecs.out-ckd ; exit 1 ; \
	fi

escjava: $(ALL_GENERATED_JAVA)
	$(ESCJAVA) $(ESCJAVAFLAGS) $(ALL_JAVA)

checksomespecs: $(ALL_GENERATED_JAVA)
	$(JML) $(JMLFLAGS) JMLInteger.java JMLChar.java JMLString.java
	$(JML) $(JMLFLAGS) JMLShort.java JMLByte.java JMLLong.java
	$(JML) $(JMLFLAGS) JMLListObjectNode.java 
	$(JML) $(JMLFLAGS) JMLValueSequence.java JMLValueSequenceEnumerator.java 
	$(JML) $(JMLFLAGS) JMLValueSet.java JMLValueSetEnumerator.java 
	$(JML) $(JMLFLAGS) JMLValueBag.java JMLValueBagEnumerator.java 
	$(JML) $(JMLFLAGS) JMLValueToObjectMap.java 
	$(JML) $(JMLFLAGS) JMLObjectToValueRelation.java JMLValueToValueRelationEnumerator.java 
	$(JML) $(JMLFLAGS) JMLType.java JMLValueType.java JMLObjectType.java 
	$(JML) $(JMLFLAGS) JMLModelObjectSet.jml 
	$(JML) $(JMLFLAGS) JMLFiniteInteger.java JMLPositiveInfinity.java
	$(JML) $(JMLFLAGS) JMLNullSafe.java

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
	$(RM) classes.stamp buildtests.stamp \
		$(PROJ_CLASSROOT)/$(subst .,/,$(PACKAGE))/JML[A-L]*.class
	$(RM) $(PROJ_CLASSROOT)/$(subst .,/,$(PACKAGE))/JML[M-Z]*.class
	$(RM) $(PROJ_CLASSROOT)/$(subst .,/,$(PACKAGE))/*.class
	$(RM) *.*-ckd core *.out java.stamp

distclean-this:	distclean-local

distclean-local:
	$(RM) stylesheet.css package-list $(ALL_GENERATED_JAVA) 
	$(RM) -r org

distclean-javadocs:
	$(RM) -r $(JAVADOCDIR)/org/jmlspecs/models

## -------------------------------------------------------------
## Global defaults

include $(TOPDIR)/Make.ProjDefs
