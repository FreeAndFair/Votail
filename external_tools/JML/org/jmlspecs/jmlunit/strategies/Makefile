##
## Copyright (C) 2003 Iowa State University
## 
## This file is part of JML
##
## JML is free software; you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 2, or (at your option)
## any later version.
##
## JML is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with JML; see the file COPYING.  If not, write to
## the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
##
## $Id: Makefile,v 1.29 2004/02/08 17:32:08 leavens Exp $
##

## ----------------------------------------------------------------- 
## At the bottom of this file we import $(TOPDIR)/Make.ProjDefs.  See the
## that file for substantial documentation.
## ----------------------------------------------------------------- 

TOPDIR =	../../../..

SUBDIRS =
TESTDIRS =

PACKAGE =	org.jmlspecs.jmlunit.strategies

RAC_CLASSES_DIR = $(TOPDIR)/raccompiled/$(subst .,/,$(PACKAGE))
NONFRAC_CLASSES_DIR = $(TOPDIR)/nonFraccompiled/$(subst .,/,$(PACKAGE))

NUMERICTYPECAPS = Byte Short Int Long Float Double
VALUETYPECAPS = $(NUMERICTYPECAPS) Char Boolean

# When you change this, you also have to change _ValueType.sh!
ALL_GENERATED_JAVA = \
		$(addsuffix AbstractFilteringIteratorDecorator.java,$(VALUETYPECAPS)) \
		$(addsuffix AbstractFilteringStrategyDecorator.java,$(VALUETYPECAPS)) \
		$(addsuffix AbstractIterator.java,$(VALUETYPECAPS)) \
		$(addsuffix AbstractStrategy.java,$(VALUETYPECAPS)) \
		$(addsuffix ArrayIterator.java,$(VALUETYPECAPS)) \
		$(addsuffix CompositeIterator.java,$(VALUETYPECAPS)) \
		$(addsuffix CompositeStrategy.java,$(VALUETYPECAPS)) \
		$(addsuffix ExtensibleStrategy.java,$(VALUETYPECAPS)) \
		$(addsuffix ExtensibleStrategyDecorator.java,$(VALUETYPECAPS)) \
		$(addsuffix Iterator.java,$(VALUETYPECAPS)) \
		$(addsuffix StrategyType.java,$(VALUETYPECAPS)) \
		$(addsuffix NonNegativeIteratorDecorator.java,$(NUMERICTYPECAPS)) \
		$(addsuffix NonNegativeStrategyDecorator.java,$(NUMERICTYPECAPS)) \


# When you change this, you also have to change the list above
VALUETYPEGENERICS = \
		_ValueType_AbstractFilteringIteratorDecorator.java-generic \
		_ValueType_AbstractFilteringStrategyDecorator.java-generic \
		_ValueType_AbstractIterator.java-generic \
		_ValueType_AbstractStrategy.java-generic \
		_ValueType_ArrayIterator.java-generic \
		_ValueType_CompositeIterator.java-generic \
		_ValueType_CompositeStrategy.java-generic \
		_ValueType_ExtensibleStrategy.java-generic \
		_ValueType_ExtensibleStrategyDecorator.java-generic \
		_ValueType_Iterator.java-generic \
		_ValueType_StrategyType.java-generic \
		_ValueType_StrategyTypeTest.java-generic \
		_ValueType_NonNegativeIteratorDecorator.java-generic \
		_ValueType_NonNegativeStrategyDecorator.java-generic \


testmacros:
	echo $(ALL_GENERATED_JAVA)

## FILES
JAVAFILES +=	$(subst .java,,$(ALL_GENERATED_JAVA)) \
		$(addsuffix Strategy,$(VALUETYPECAPS)) \
		$(addsuffix BigStrategy,$(VALUETYPECAPS)) \
		AbstractFilteringIteratorDecorator \
		AbstractFilteringStrategyDecorator \
		AbstractExtensibleStrategyDecorator \
		CachedObjectAbstractStrategy	\
		CloneableObjectArrayAbstractIterator	\
		CloneableObjectAbstractStrategy	\
		CloneableObjectAbstractExtensibleStrategyDecorator \
		CollectionStrategy		\
		CompositeIterator		\
		CompositeStrategy		\
		EmptyNewObjectIterator		\
		ImmutableObjectArrayIterator	\
		ImmutableObjectAbstractStrategy	\
		ImmutableObjectExtensibleStrategyDecorator \
		IndefiniteIterator		\
		IndefiniteIteratorUtilities	\
		IteratorAbstractAdapter		\
		NewObjectAbstractExtensibleStrategyDecorator \
		NewObjectAbstractStrategy	\
		NewObjectAbstractIterator	\
		NonNullIteratorDecorator	\
		NonNullStrategyDecorator	\
		ObjectStrategy	\
		ObjectArrayAbstractIterator	\
		StrategyType		\
		StringStrategy		\
		JMLCollectionStrategy \
		JMLTypeStrategy \
		TestSuiteFullException	\

NAMESTOTEST = \
		CharIterator \
		CloneableObjectArrayAbstractIterator \
		CompositeIterator \
		DoubleAbstractFilteringIteratorDecorator \
		DoubleCompositeIterator \
		ImmutableObjectArrayIterator \
		IntArrayIterator \
		NewObjectAbstractIterator \
		NonNullIteratorDecorator


ALL_JAVA = $(addsuffix .java,$(JAVAFILES))

TESTFILES = $(addsuffix _JML_Test,$(NAMESTOTEST)) \
		$(addsuffix StrategyTypeTest,$(NUMERICTYPECAPS)) \
		CharStrategyTypeTest BooleanStrategyTypeTest \
		StringStrategyTest ObjectStrategyTest \
		ImmutableObjectAbstractStrategyTest \
		CloneableObjectAbstractStrategyTest \
		NewObjectAbstractStrategyTest \
		CompositeStrategyTest \
		NonNullStrategyDecoratorTest


TESTDATACLASSFILES = $(addsuffix _JML_TestData.class,$(NAMESTOTEST))

GENFILES = $(addsuffix _JML_Test.java,$(NAMESTOTEST))

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

## ----------------------------------------------------------------------
## GOALS

default:	build buildtests

build-this:	classes

build-this-before: generate non-jmlc-files-compile

NONJMLCFILES += LimitedTestSuite \
		ConstructorFailed

non-jmlc-files-compile: $(addsuffix .class,$(NONJMLCFILES))

generate: $(ALL_GENERATED_JAVA)

# !FIXME! there should be a better way to generate all of these...
$(ALL_GENERATED_JAVA): _ValueType_.sh $(VALUETYPEGENERICS)
	./_ValueType_.sh

## -------------------------------------------------------------
## Testing

check: runtests-this-start checkallspecs runtests-this-end

buildtests-this-before: generate java.stamp

java.stamp: $(addsuffix .java,$(NAMESTOTEST))
	$(JMLUNIT) $(JMLUNITFLAGS) $?
	touch java.stamp

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

# Clean up stuff
#
clean-this:	cleanlocal

cleanlocal: 
	$(RM) *.*-ckd core *.out java.stamp

distclean-this:	distclean-local

distclean-local:
	$(RM) stylesheet.css package-list $(ALL_GENERATED_JAVA) 
	$(RM) -r org

## ----------------------------------------------------------------------
## GLOBAL DEFINITIONS

include $(TOPDIR)/Make.ProjDefs
