# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.32 2005/07/09 20:18:09 leavens Exp $

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

TOPDIR = ../../..
PACKAGE = org.jmlspecs.samples

JAVAFLAGS = -g

SUBDIRSWITHTESTS = dbc digraph list jmlkluwer jmlrefman jmltutorial \
		misc prelimdesign reader sets stacks table 
SUBDIRS = $(SUBDIRSWITHTESTS) \
	  dirobserver 
# leave TESTDIRS empty so tests don't recurse into them by default.
TESTDIRS = 
TESTSUITES = $(SUBDIRSWITHTESTS)

default: runtests

all: check

check: runtests-this-start \
	checkallspecs compile compileallspecs \
	runtests-this-end

runtests-helper: runtests-this-start runtests-this runtests-this-end

# The test in the if below checks if there are any subdirectories
# with skip files; the test is true when there are none.
# In the true case, we just use jml -R, which is faster
# than recursing into each subdirectory.
runtests-this:
	@if test '*/skip' = `echo */skip`; \
	then \
		echo $(JML) $(JMLFLAGS) -R .; \
		$(JML) $(JMLFLAGS) -R .; \
	else \
		for dir in $(SUBDIRS) ; \
		do \
		    if test -d $$dir; \
	            then \
			$(MAKE) -C $$dir runtests-helper; \
		    fi; \
		done; \
	fi

ifdef ALLTESTS
runtests-this: compile TestSuite.out
endif

# check all JML specs.
checkallspecs: buildtests
	if $(JML) $(JMLFLAGS) -R . > checkallspecs.out-ckd 2>&1 ; \
	then cat checkallspecs.out-ckd ; \
	else cat checkallspecs.out-ckd ; exit 1 ; \
	fi

compileallspecs:
	$(MAKE) JML='java org.jmlspecs.jmlrac.Main' checkallspecs

TestSuite.out: raccompile-static $(TESTRUNFILES) TestSuite.class 
	env CLASSPATH="$(RAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.out
	@grep -q 'FAILURES!!!' TestSuite.out && exit 1 || exit 0

raccompile-static: 
	$(MAKE) -C ../lang raccompile-static
	$(MAKE) -C ../models raccompile-static
	for d in $(SUBDIRSWITHTESTS) ; \
	do \
		make -C $$d raccompile-static ; \
	done

TestSuite.dout: raccompile-dynamic $(TESTRUNFILES) TestSuite.class 
	env CLASSPATH="$(NONFRAC_CLASSES_JTOP)$(JPATHSEP)"'$(CLASSPATH)' \
		$(JUNITFORJML) $(PACKAGE).TestSuite 2>&1 | tee TestSuite.dout
	@grep -q 'FAILURES!!!' TestSuite.dout && exit 1 || exit 0

raccompile-dynamic:
	$(MAKE) -C ../lang raccompile-dynamic
	$(MAKE) -C ../models raccompile-dynamic
	for d in $(SUBDIRSWITHTESTS) ; \
	do \
		make -C $$d raccompile-dynamic ; \
	done

# Clean up stuff
#
clean-this : cleanlocal

cleanlocal:
	$(RM) *.*-ckd core

clean-classes-this: remove-dot-class-files

include $(TOPDIR)/Make.ProjDefs
