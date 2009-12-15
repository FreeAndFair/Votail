# @(#)$Id: Makefile,v 1.28 2008/01/10 02:42:46 leavens Exp $

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

WWWMACHINE = monroe.cs.ucf.edu
WWW_DIR = /home/leavens/WWW/JML
FTPMACHINE = $(WWWMACHINE)
FTP_DIR = /home/leavens/WWW/JML/OldReleases
ANONFTPMACHINE = $(WWWMACHINE)
ANONFTPDIR = /home/leavens/WWW/tech-reports/

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
EPSTOPDF = epstopdf

# DVIPS = dvips
DVIPS = dvips -Pcmz -Pamz -f
DVI2PDF = dvipdft
PS2PDF = ps2pdf

CP = cp
RM = rm -f
DELTREE = $(RM) -r

# don't permenantly change the definition of paper,
# as it's depended on by the JML release
paper =		jmldbc

texfiles =	$(wildcard *.tex)

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

PDFFIGFILES =	fig-postcondition-meaning.pdf \
		fig-abstraction-function.pdf

TOPDIR = ../..
SAMPLESDIR = $(TOPDIR)/org/jmlspecs/samples/jmltutorial

SAMPLES = samples

SAMPLEFILES = \
		$(SAMPLES)/Person.java \
		$(SAMPLES)/PersonMain.java \
		$(SAMPLES)/Person.refines-java \
		$(SAMPLES)/SqrtExample.java

PERL = perl
## Take out the copyright notice and the following 2 lines.
## from the Java files.
STRIPCODE=$(PERL) -e 'while (<>) { s/\r//g; if (/^\/\/ the Free Software Foundation, 675 Mass Ave/) { $$seen = 1; $$past = -2; }; print if ($$seen && $$past++ > 0); }'

default jotarticle: paper.tex $(PDFFIGFILES)
	$(PDFLATEX) $<

all:	$(dvifiles) $(psfiles) $(pdffiles)

build buildtests:

$(SAMPLES)/%.java : $(SAMPLESDIR)/%.java Makefile
	@$(STRIPCODE) $< > $@

$(SAMPLES)/%.refines-java : $(SAMPLESDIR)/%.refines-java Makefile
	@$(STRIPCODE) $< > $@

%.pdf: %.eps
	$(EPSTOPDF) $<

%.ps: %.dvi
	$(DVIPS) -q -o $@ $<

%.ps.gz: %.ps
	gzip -c $< > $@

# prefer ps2pdf because this seems to work better for Gary making releases...
# and it's quieter
%.pdf: %.ps
	which $(PS2PDF) >/dev/null 2>/dev/null \
	&& $(PS2PDF) $<  >/dev/null \
	|| $(DVI2PDF) -q $(*F) >/dev/null

%.pdf.gz: %.pdf
	gzip -c $< > $@

%.class: %.java
	$(JAVAC) $(JAVAFLAGS) $<

paper.aux:  $(SAMPLEFILES) $(PDFFIGFILES)
	$(PDFLATEX) paper.tex

paper.bbl: paper.bib paper.aux
	$(BIBTEX) paper

paper.tex: $(SAMPLEFILES) $(PDFFIGFILES) paper.bbl

${paper}.aux: $(SAMPLEFILES)
	$(LATEX) ${paper}.tex

${paper}.bbl: ${paper}.bib ${paper}.aux
	$(BIBTEX) ${paper}

${paper}.tex: $(SAMPLEFILES) ${paper}.bbl

dvi ${paper}.dvi: ${paper}.tex
	$(LATEX) ${paper}; $(LATEX) ${paper} 

postscript : ${paper}.ps

pdf: ${paper}.pdf

# we use the PDF file in the HTML (for now)
html :
	@$(MAKE) pdf cleansamples >/dev/null

# there are also no info files
info:

publish: ftp-docs www

ftp-docs: docs-for-ftp just-ftp-docs

docs-for-ftp: $(paper).pdf html

just-ftp-docs: real-ftp dummy-tr

www: real-www

real-ftp:
	ssh $(FTPMACHINE) $(RM) $(FTP_DIR)/${paper}.pdf
	scp -pq ${paper}.pdf $(FTPMACHINE):$(FTP_DIR)
	ssh $(FTPMACHINE) chmod 644  $(FTP_DIR)/*.pdf

dummy-tr:

# do this when the ref manual is a TR
real-tr: ${paper}.pdf
	scp -pq ${paper}.pdf $(ANONFTPMACHINE):$(ANONFTPDIR)/
	scp -pq TR.abs README $(ANONFTPMACHINE):$(ANONFTPDIR)/

real-www:
	ssh $(WWWMACHINE) $(RM) $(WWW_DIR)/${paper}.pdf
	scp -pq ${paper}.pdf $(WWWMACHINE):$(WWW_DIR)/
	ssh $(WWWMACHINE) chmod 644 $(WWW_DIR)/${paper}.pdf

# Purse.class: Purse.java
# 	$(JMLC) $(JMLCFLAGS) Purse.java
# 
# Purse_JML_Test.java: Purse.java
# 	$(JMLUNIT) -L2 Purse.java
# 
# Purse.out: Purse.class Purse_JML_Test.class Purse_JML_TestData.class
# 	$(JMLRAC) Purse_JML_TestData 2>&1 | tee Purse.out
# 
# ${paper}.dvi: ${paper}.tex
# 	$(LATEX) ${paper};

clean cleanup:
	rm -f _region_* *.aux *.log *.blg

cleansamples:
	rm -f samples/*java

distclean-subdir:

distclean pristine cleanall: clean cleansamples
	rm -rf `cat .cvsignore`

rebuild-all: cleanall pdf
