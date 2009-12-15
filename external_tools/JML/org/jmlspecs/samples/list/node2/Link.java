// @(#) $Id: Link.java,v 1.4 2005/12/06 19:55:00 chalin Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

// Author:  Clyde Ruby

package org.jmlspecs.samples.list.node2;

//@ refine "Link.jml";

public /*@ pure @*/ class Link {

    // data members

    protected /*@ nullable @*/ OneWayNode node_ = null;

    // methods

    public Link() {
	node_ = null;
    }
    public Link(/*@ nullable @*/ OneWayNode node) {
	node_ = node;
    }
    public /*@ nullable @*/ Object getEntry() {
	if (node_ != null) {
	    return node_.getEntry();
	} else {
	    return null;
	}
    }
    public /*@ nullable @*/ Link getNext() {
	if (node_ != null) {
	    return node_.getNextLink();
	} else {
	    return null;
	}
    }
    public String toString() {
	if (node_ != null) {
	    return "<" + node_.toString() + ">";
	} else {
	    return "< >";
	}
    }
}

