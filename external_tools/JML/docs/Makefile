# @(#)$Id: Makefile,v 1.11 2005/07/17 17:31:57 leavens Exp $
# -*- makefile -*- for documentation directory.

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

## ----------------------------------------------------------------- 
## At the bottom of this file we import $(TOPDIR)/Make.ProjDefs.  See the
## that file for substantial documentation.
## ----------------------------------------------------------------- 

TOPDIR = ..

SUBDIRS = prelimdesign jmlkluwer jmlrefman jmltutorial

all: docs html

docs: manpage postscript

manpage:
	cd man; $(MAKE) html text; cd ..

publish dvi postscript pdf html info ftp-docs just-ftp-docs docs-for-ftp www:
	@for d in $(SUBDIRS); \
	do cd $$d; \
		$(MAKE) BIBTEX='$(BIBTEX)' \
			DVIPS='$(DVIPS)' DVIPDF='$(DVIPDF)' \
			TEXI2DVI='$(TEXI2DVI)' TEXI2HTML='$(TEXI2HTML)' $@; \
	   cd ..; \
	done

## ----------------------------------------------------------------------
## GLOBAL DEFINITIONS

include $(TOPDIR)/Make.ProjDefs
