# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.17 2008/01/10 02:42:46 leavens Exp $

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

TOPDIR = ../..

INFO_DIR = /usr/unsup/info
WWWMACHINE = monroe.cs.ucf.edu
WWW_DIR = /home/leavens/WWW/JML
FTPMACHINE = $(WWWMACHINE)
FTP_DIR = /home/leavens/WWW/JML/OldReleases

# Included JML files that are automatically generated
# from corresponding files in other directories

SAMPLESDIR = $(TOPDIR)/org/jmlspecs/samples/jmlkluwer

LOCAL		= ./local
LOCAL_TEXINFOS = \
		$(LOCAL)/PriorityQueueUser.javarefined.texinfo \
		$(LOCAL)/PriorityQueueUser.jmlrefined.texinfo \
		$(LOCAL)/PriorityQueueUser.java.texinfo \
		$(LOCAL)/QueueEntry.jmlrefined.texinfo \
		$(LOCAL)/PriorityQueue.javarefined.texinfo

TEXINFOS = $(LOCAL_TEXINFOS)

# Implicit Rules (for GNU Make)

$(LOCAL)/%.java.texinfo : $(SAMPLESDIR)/%.java
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.jml.texinfo : $(SAMPLESDIR)/%.jml
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.javarefined.texinfo : $(SAMPLESDIR)/%.java-refined
	@$(CODE2TEXI) $< > $@

$(LOCAL)/%.jmlrefined.texinfo : $(SAMPLESDIR)/%.jml-refined
	@$(CODE2TEXI) $< > $@


# Target Definitions.
#
TEXIBASE = jmlkluwer

all : html pdf $(TEXIBASE).ps.gz

postscript : $(TEXIBASE).ps

$(TEXIBASE).ps  : $(TEXIBASE).dvi

dvi: $(TEXIBASE).dvi

$(TEXIBASE).dvi : $(TEXIBASE).texinfo $(TEXINFOS)
	rm -f $(TEXIBASE).aux
	$(TEXI2DVI) $(TEXIBASE).texinfo

pdf: $(TEXIBASE).pdf

$(TEXIBASE).pdf : $(TEXIBASE).texinfo $(TEXINFOS)
	$(TEXI2PDF) $(TEXIBASE).texinfo

$(TEXIBASE).dvi.gz : $(TEXIBASE).dvi
	gzip -f --best $(TEXIBASE).dvi

$(TEXIBASE).ps.gz : $(TEXIBASE).ps
	gzip -f --best $(TEXIBASE).ps

info : $(TEXIBASE).info

$(TEXIBASE).info : $(TEXIBASE).texinfo $(TEXINFOS)
	$(MAKEINFO) $(TEXIBASE).texinfo

texinfos: $(TEXINFOS)


html: $(TEXIBASE)/$(TEXIBASE)_toc.html

$(TEXIBASE)/$(TEXIBASE)_toc.html: $(TEXIBASE).texinfo $(TEXINFOS) \
					adjust-html-file
	@$(DELTREE) $(TEXIBASE)
	@$(MKDIR) $(TEXIBASE)
	@$(TEXI2HTML) $(TEXI2HTMLOPTS) $(TEXIBASE).texinfo
	@if test '!' -f $(TEXIBASE)_toc.html ; \
	then mv $(TEXIBASE)/*.html . ; \
	fi
	@for f in *.html ; \
	do \
		$(PERL) -p adjust-html-file $$f > $(TEXIBASE)/$$f ; \
	done
	@-$(CP) $(TEXIBASE)/$(TEXIBASE)_toc.html $(TEXIBASE)/index.html
	@$(RM) $(TEXIBASE)*.html
	@$(MAKE) cleansamples

publish: ftp-docs www

ftp-docs: docs-for-ftp just-ftp-docs

docs-for-ftp: $(TEXIBASE).ps.gz $(TEXIBASE).pdf html

just-ftp-docs:
	ssh $(FTPMACHINE) $(RM) $(FTP_DIR)/$(TEXIBASE).ps.gz
	ssh $(FTPMACHINE) $(RM) $(FTP_DIR)/$(TEXIBASE).pdf
	scp -q $(TEXIBASE).ps.gz $(TEXIBASE).pdf $(FTPMACHINE):$(FTP_DIR)
	ssh $(FTPMACHINE) chmod 644 $(FTP_DIR)/$(TEXIBASE).*.gz $(FTP_DIR)/*.pdf

www: html
	chmod u+w $(TEXIBASE) $(TEXIBASE)/*.html
	chmod a+r $(TEXIBASE)/*.html
	chmod a+rx $(TEXIBASE)
	ssh $(WWWMACHINE) $(DELTREE) $(WWW_DIR)/$(TEXIBASE)
	scp -prq $(TEXIBASE) $(WWWMACHINE):$(WWW_DIR)/

# Clean up stuff
#
clean-this: cleanlocal

cleanlocal:
	$(RM) *.log *.blg *.*-ckd core *.class
	$(RM) $(TEXINFOS)
	$(RM) $(TEXIBASE).aux $(TEXIBASE).cp $(TEXIBASE).cps \
		$(TEXIBASE).fn $(TEXIBASE).ky $(TEXIBASE).log \
		$(TEXIBASE).pg $(TEXIBASE).pgs $(TEXIBASE).toc \
		$(TEXIBASE).tp $(TEXIBASE).vr

clean-classes-this: remove-dot-class-files

distclean-this: distclean-local

distclean-local: cleanhtmldir cleansamples

cleanhtmldir:
	$(DELTREE) $(TEXIBASE)

cleansamples:
	@$(RM) $(LOCAL)/*.texinfo

# include standard project targets

include $(TOPDIR)/Make.ProjDefs
