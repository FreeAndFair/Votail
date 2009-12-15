# -*- makefile -*- mode for emacs
# @(#)$Id: Makefile,v 1.36 2008/01/10 02:42:46 leavens Exp $

# Copyright (C) 2002 Iowa State University

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

TOPDIR	= ../..

# Included JML files that are automatically generated
# from corresponding files in other directories
SAMPLESDIR = $(TOPDIR)/org/jmlspecs/samples/jmlrefman
DIROBSERVERSAMPLESDIR = $(TOPDIR)/org/jmlspecs/samples/dirobserver

#INFO_DIR = /usr/unsup/info
INFO_DIR = info
WWWMACHINE = monroe.cs.ucf.edu
WWW_DIR = /home/leavens/WWW/JML
FTPMACHINE = $(WWWMACHINE)
FTP_DIR = /home/leavens/WWW/JML/OldReleases

# texinfo files included by jml.texinfo
GRAM_TEXINFO	= collected-grammar.texinfo
GRAMMAR_HTML 	= jmlrefman_21.html

# JML files included by jml.texinfo or $(TEXINFOS); automatically
# generated from corresponding files in $(SAMPLESDIR)
LOCAL		= local
LOCAL_NAMES = \
		Constraint.java \
		Diverges.spec \
		IntHeap.java \
		Invariant.java \
		GhostLocals.java \
		Heavyweight.java \
		ImplicitOld.java \
		InconsistentMethodSpec.java \
		InconsistentMethodSpec2.java \
		RefineDemo.jml-refined \
		RefineDemo.jml \
		RefineDemo.java \
		RefineDemo2.jml-refined \
		RefineDemo2.jml \
		RefineDemo2.java \
		SignalsClause.java \
		Lightweight.java \
		SumArrayLoop.java 

LOCAL_TEXINFOS = $(addprefix $(LOCAL)/,$(addsuffix .texinfo,$(LOCAL_NAMES)))

# JML files included by jml.texinfo or $(TEXINFOS); automatically
# generated from corresponding files in $(DIROBSERVERSAMPLESDIR)
DIROBSERVER	= dirobserver
DIROBSERVER_NAMES = \
		Directory.java

DIROBSERVER_TEXINFOS = $(addprefix $(DIROBSERVER)/,$(addsuffix .texinfo,$(DIROBSERVER_NAMES)))

TEXINFOS = $(GRAM_TEXINFO) $(LOCAL_TEXINFOS) $(DIROBSERVER_TEXINFOS)

SAMPLE_SOURCES = $(addprefix $(SAMPLESDIR)/,$(LOCAL_NAMES))

# Implicit Rules (for GNU Make)

$(LOCAL)/%.jml.texinfo : $(SAMPLESDIR)/%.jml
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.java.texinfo : $(SAMPLESDIR)/%.java
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.spec.texinfo : $(SAMPLESDIR)/%.spec
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.refines-jml.texinfo : $(SAMPLESDIR)/%.refines-jml
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.refines-java.texinfo : $(SAMPLESDIR)/%.refines-java
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.refines-spec.texinfo : $(SAMPLESDIR)/%.refines-spec
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.jml-refined.texinfo : $(SAMPLESDIR)/%.jml-refined
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.java-refined.texinfo : $(SAMPLESDIR)/%.java-refined
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.spec-refined.texinfo : $(SAMPLESDIR)/%.spec-refined
	@$(CODE2TEXI) $< > $@

$(DIROBSERVER)/%.jml.texinfo : $(DIROBSERVERSAMPLESDIR)/%.jml
	@$(CODE2TEXI) $< > $@

$(DIROBSERVER)/%.java.texinfo : $(DIROBSERVERSAMPLESDIR)/%.java
	@$(CODE2TEXI) $< > $@

$(DIROBSERVER)/%.spec.texinfo : $(DIROBSERVERSAMPLESDIR)/%.spec
	@$(CODE2TEXI) $< > $@


# Target Definitions.
#
TEXIBASE = jmlrefman

## Note: since each target must work stand-alone, each target 
## copies and then cleans up the sample code files that are 
## referenced by the jmlrefman.texinfo file.  It is desired that
## these be deleted after any make task so they do not end up in 
## releases. (They are texinfo versions of code snippets, not actually
## legal java.)
.PHONY: all
all :  pdf $(TEXIBASE).ps.gz html

.PHONY: copy-samples
copy-samples: $(LOCAL) $(TEXINFOS)

$(LOCAL):
	mkdir $(LOCAL)

$(DIROBSERVER):
	mkdir $(DIROBSERVER)

.PHONY: postscript
postscript: local $(TEXIBASE).ps

$(TEXIBASE).ps : $(TEXIBASE).dvi

.PHONY: dvi
dvi: local $(TEXIBASE).dvi

$(TEXIBASE).dvi : $(TEXIBASE).texinfo $(SAMPLE_SOURCES)
	$(MAKE) copy-samples
	rm -f $(TEXIBASE).aux
	$(TEXI2DVI) $(TEXIBASE).texinfo
	$(MAKE) cleansamples

.PHONY: pdf
pdf: local $(TEXIBASE).pdf

$(TEXIBASE).pdf: $(TEXIBASE).texinfo $(SAMPLE_SOURCES)
	$(MAKE) copy-samples
	$(TEXI2PDF) $(TEXIBASE).texinfo
	$(MAKE) cleansamples

$(TEXIBASE).dvi.gz : $(TEXIBASE).dvi
	gzip -f --best $(TEXIBASE).dvi

$(TEXIBASE).ps.gz : $(TEXIBASE).ps
	gzip -f --best $(TEXIBASE).ps

.PHONY: grammar
grammar: grammar.pdf

grammar.ltx: grammar.texinfo collected-grammar.texinfo
	texi2latex grammar.texinfo

grammar.pdf: grammar.ltx
	pdflatex grammar.ltx

.PHONY: info
info: local $(TEXIBASE).info

$(TEXIBASE).info : $(TEXIBASE).texinfo $(SAMPLE_SOURCES)
	$(MAKE) copy-samples
	$(MAKEINFO) $(TEXIBASE).texinfo
	$(MAKE) cleansamples


.PHONY: html
html: local $(TEXIBASE)/$(TEXIBASE)_toc.html

$(TEXIBASE)/$(TEXIBASE)_toc.html: $(TEXIBASE).texinfo $(SAMPLE_SOURCES) \
				adjust-html-file adjust-grammar-file Makefile
	$(MAKE) copy-samples
	rm -fr $(TEXIBASE)
	mkdir $(TEXIBASE)
	$(TEXI2HTML) $(TEXI2HTMLOPTS) $(TEXIBASE).texinfo
	@if test '!' -f $(TEXIBASE)_toc.html ; \
	then mv $(TEXIBASE)/*.html . ; \
	fi
	@for f in `ls *.html| grep -v $(GRAMMAR_HTML)` ; \
	do \
		$(PERL) -p adjust-html-file $$f  > $(TEXIBASE)/$$f ; \
	done
	@$(PERL) -p adjust-grammar-file $(GRAMMAR_HTML) >$(TEXIBASE)/$(GRAMMAR_HTML)
	-$(CP) $(TEXIBASE)/$(TEXIBASE)_toc.html $(TEXIBASE)/index.html
	rm -f *.html
	$(MAKE) cleansamples

$(GRAM_TEXINFO) : $(TEXIBASE).texinfo collect-grammar.sh
	./collect-grammar.sh $(TEXIBASE).texinfo > $@

publish: ftp-docs www

ftp-docs: docs-for-ftp just-ftp-docs

docs-for-ftp: $(TEXIBASE).ps.gz $(TEXIBASE).pdf html

just-ftp-docs: real-ftp dummy-tr

www: html real-www

real-ftp:
	ssh $(FTPMACHINE) $(RM) $(FTP_DIR)/$(TEXIBASE).ps.gz
	ssh $(FTPMACHINE) $(RM) $(FTP_DIR)/$(TEXIBASE).pdf
	scp -pq $(TEXIBASE).ps.gz $(TEXIBASE).pdf $(FTPMACHINE):$(FTP_DIR)
	ssh $(FTPMACHINE) chmod 644 $(FTP_DIR)/$(TEXIBASE).*.gz $(FTP_DIR)/*.pdf

dummy-tr:

real-www:
	chmod u+w $(TEXIBASE) $(TEXIBASE)/*.html
	chmod a+r $(TEXIBASE)/*.html
	chmod a+rx $(TEXIBASE)
	ssh $(WWWMACHINE) $(DELTREE) $(WWW_DIR)/$(TEXIBASE)
	scp -prq $(TEXIBASE) $(WWWMACHINE):$(WWW_DIR)/

# Clean up stuff
#
clean-this : cleanlocal

cleanlocal:
	rm -f $(TEXIBASE).aux $(TEXIBASE).cp $(TEXIBASE).cps $(TEXIBASE).fn \
	      $(TEXIBASE).ky $(TEXIBASE).log $(TEXIBASE).pg $(TEXIBASE).pgs $(TEXIBASE).toc $(TEXIBASE).tp $(TEXIBASE).vr
	rm -f grammar.ltx grammar.pdf

distclean-this : distclean-local

distclean-local: cleanhtmldir cleansamples
	-$(RM) $(LOCAL)/*.texinfo $(GRAM_TEXINFO)
	-$(RM) $(DIROBSERVER)/*.texinfo $(GRAM_TEXINFO)
	$(RM) core $(TEXIBASE).info* $(TEXIBASE).dvi $(TEXIBASE).ps *~

cleanhtmldir:
	$(DELTREE) $(TEXIBASE)

cleansamples:
	$(RM) $(LOCAL)/*.texinfo
	$(RM) $(DIROBSERVER)/*.texinfo

# include standard project targets

include $(TOPDIR)/Make.ProjDefs
