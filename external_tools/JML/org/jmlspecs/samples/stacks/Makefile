# -*- makefile -*- mode for emacs
# @(#) $Id: Makefile,v 1.11 2004/06/15 23:12:42 leavens Exp $

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

PACKAGE = org.jmlspecs.samples.stacks

JAVAFILES = 	BoundedStack \
	    	BoundedStackException \
		BoundedStackImplementation \
		BoundedStackInterface \
		BoundedThing \
		UnboundedStack \
		UnboundedStack2 \
		UnboundedStackAsArrayList \
		UnboundedStackRC \
		UnboundedStackRC2

NAMESTOTEST = BoundedStackInterface UnboundedStackAsArrayList

# !FIXME! This doesn't test the constructors in BoundedStackImplementation
# and it's not testing clone either.

include ../Make.CommonDefs
