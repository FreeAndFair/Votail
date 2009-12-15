# @(#)$Id: Makefile,v 1.14 2005/05/31 02:26:07 leavens Exp $

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

JAVAC = javac
JAVACFLAGS = 
JMLC = jmlc
JMLCFLAGS = -Q -a
JMLUNIT = jmlunit
JAVA = java
JMLRAC = jmlrac
LATEX = latex
PDFLATEX = pdflatex
BIBTEX = bibtex

paper =		sttt

texfiles =	$(addsuffix .tex,$(paper))

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

all:	$(dvifiles) $(psfiles) $(pdffiles)

%.pdf: %.tex
	pdflatex $< $@

%.pdf.gz: %.pdf
	gzip -c $< > $@

%.ps: %.dvi
	dvips -Pcmz -Pamz -f < $< > $@

%.ps.gz: %.ps
	gzip -c $< > $@

%.class: %.java
	$(JAVAC) $(JAVAFLAGS) $<

${paper}.dvi: Purse.java jmllogo.eps ${paper}.tex
	$(LATEX) ${paper}; $(LATEX) ${paper}; $(BIBTEX) ${paper}; \
	$(LATEX) ${paper}; $(LATEX) ${paper};

${paper}.pdf: Purse.java jmllogo.pdf ${paper}.tex
	$(PDFLATEX) ${paper}; $(PDFLATEX) ${paper}; $(BIBTEX) ${paper}; \
	$(PDFLATEX) ${paper}; $(PDFLATEX) ${paper};

jmllogo.pdf: jmllogo.eps
	ps2pdf jmllogo.eps

Purse.class: Purse.java
	$(JMLC) $(JMLCFLAGS) Purse.java

Purse_JML_Test.java: Purse.java
	$(JMLUNIT) -L2 Purse.java

Purse.out: Purse.class Purse_JML_Test.class Purse_JML_TestData.class
	$(JMLRAC) Purse_JML_Test 2>&1 | tee Purse.out

Purse.dout: Purse.class Purse_JML_Test.class Purse_JML_TestData.class
	$(JMLRAC) Purse_JML_Test 2>&1 | tee Purse.dout

Purse2.class: Purse2.java
	$(JMLC) $(JMLCFLAGS) Purse2.java

Purse2_JML_Test.java: Purse2.java
	$(JMLUNIT) -L2 Purse2.java

Purse2.out: Purse2.class Purse2_JML_Test.class Purse2_JML_TestData.class
	$(JMLRAC) Purse2_JML_Test 2>&1 | tee Purse2.out

Purse2.dout: Purse2.class Purse2_JML_Test.class Purse2_JML_TestData.class
	$(JMLRAC) Purse2_JML_Test 2>&1 | tee Purse2.dout

clean cleanup:
	rm -f _region_* *.aux *.log *.blg \
		${paper}.dvi ${paper}.ps ${paper}.pdf jmllogo.pdf

pristine cleanall: clean
	rm -rf `cat .cvsignore`
