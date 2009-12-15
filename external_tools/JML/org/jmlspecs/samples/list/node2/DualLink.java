// @(#) $Id: DualLink.java,v 1.5 2005/12/09 04:20:15 leavens Exp $

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

//@ refine "DualLink.jml";

public /*@ pure @*/ class DualLink extends Link { // Dual Directional Node

    // data members

    protected /*@ nullable @*/ TwoWayNode dualNode_ = null;

    // methods

    public DualLink() {
	dualNode_ = null;
	node_ = null;
    }
    public DualLink(/*@ nullable @*/ TwoWayNode node) {
	node_ = node;
	dualNode_ = node; // so no need for downcasting
    }
    public /*@ nullable @*/ DualLink getPrevious() {
	if (dualNode_ != null) {
	    return dualNode_.getPrevLink();
	} else {
	    return null;
	}
    }
}

