# -*- makefile -*- mode for emacs
# @(#)$Id: Makefile,v 1.12 2008/03/04 23:28:17 wahlst Exp $

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

## Note: in this directory, the .txt and the .html files are
## generated, but are still under CVS control.  This is because
## generation requires specialized tools that not everyone has or can
## run successfully.  So first check in the .1 files, then do a
## "make", then commit the products, if you can do that.  If you can't
## generate the products, talk to someone who can (like Gary).

TOPDIR = ../..

NROFF = nroff
TROFF = groff

%.txt: %.1
	$(NROFF) -man $< | col -b > $@

%.ps: %.1
	$(TROFF) -man -T ps $< > $@

%.html: %.1
	$(TROFF) -man -T html $< > $@

all: text html

MANPAGES = jml jmlc jmldoc jmlrac jmlunit jtest jml-junit jmlspec jmle jmlre jml-launcher

text: $(addsuffix .txt,$(MANPAGES))

html: $(addsuffix .html,$(MANPAGES))

insert:
	for i in `ls *.insert.1`; do \
		./insert.sh `echo $$i | sed -e "s/.insert.1//"` ;\
	done

# Clean up stuff
#
clean-this: cleanlocal

cleanlocal:
	rm -f *.ps *.dvi

clean-classes-this: remove-dot-class-files

# include standard project targets

include $(TOPDIR)/Make.ProjDefs
