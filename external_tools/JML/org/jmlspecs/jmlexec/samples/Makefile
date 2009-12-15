## 
## Copyright (C) 2000-2001 Iowa State University
## 
## This file is part of mjc, the MultiJava Compiler.
## 
## based in part on work:
## 
## Copyright (C) 1990-99 DMS Decision Management Systems Ges.m.b.H.
##
## This program is free software; you can redistribute it and/or modify
## it under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 2 of the License, or
## (at your option) any later version.
##
## This program is distributed in the hope that it will be useful,
## but WITHOUT ANY WARRANTY; without even the implied warranty of
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
## GNU General Public License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program; if not, write to the Free Software
## Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
##
## $Id: Makefile,v 1.4 2008/03/28 19:41:21 wahlst Exp $
##

## ----------------------------------------------------------------- 
## At the bottom of this file we import $(TOPDIR)/Make.ProjDefs.  See the
## that file for substantial documentation.
## ----------------------------------------------------------------- 

TOPDIR =	../../../..
PACKAGE =	org/jmlspecs/jmlexec/samples
JMLRE = $(JAVA)

## ----------------------------------------------------------------------
## GOALS

IntList.class: IntList.jml
	$(JMLE) IntList.jml

Graph.class: Graph.jml
	$(JMLE) Graph.jml

Digraph.class: Digraph.jml ArcType.jml NodeType.java Node.jml
	$(JMLE) Digraph.jml ArcType.jml NodeType.java Node.jml

.PHONY: specs
specs: IntList.class Graph.class Digraph.class

.PHONY: drivers
drivers: TestGraph.class TestIntList.class TestDigraph.class


buildsamples: specs drivers

run: buildsamples
	$(JMLRE) org.jmlspecs.jmlexec.samples.TestIntList
	$(JMLRE) org.jmlspecs.jmlexec.samples.TestGraph
	$(JMLRE) org.jmlspecs.jmlexec.samples.TestDigraph

default: buildsamples

## ----------------------------------------------------------------------
## GLOBAL DEFINITIONS

include $(TOPDIR)/Make.ProjDefs
