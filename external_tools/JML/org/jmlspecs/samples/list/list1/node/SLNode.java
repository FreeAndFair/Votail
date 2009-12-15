// @(#) $Id: SLNode.java,v 1.8 2007/07/01 02:38:46 chalin Exp $

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

package org.jmlspecs.samples.list.list1.node;

//@ refine "SLNode.jml";

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class SLNode { // Singly Linked Node

    // data members

    protected Object entry_;
    protected SLNode nextNode_;

    // methods

    public SLNode(Object ent) {
	entry_ = ent;
	nextNode_ = null;
    }
    public /*@ pure @*/ Object getEntry() {
	return entry_;
    }
    public void setEntry(Object newEntry) {
	entry_ = newEntry;
    }
    public /*@ pure @*/ SLNode getNextNode() {
	return nextNode_;
    }
    public void insertAfter(Object newEntry) {
	nextNode_ = new SLNode(newEntry, nextNode_);
    }
    public void removeNextNode() {
	if (nextNode_ != null) {
	    nextNode_ = nextNode_.getNextNode();
	}
    }
    public /*@ non_null @*/ Object clone() {
	if (nextNode_ == null) {
	    return new SLNode(getEntry());
	} else {
	    return new SLNode(getEntry(), (SLNode)nextNode_.clone());
	}
    }
    public /*@ pure non_null @*/ String toString() {
	return getEntry() + ", " + stringOfEntries(getNextNode());
    }

    /** Returns the string concatentation of all nodes following this node up
     * to and excluding the end of the chain or this, which ever is reached
     * first (i.e. this method will terminate even for circular lists).
     */
    protected /*@ pure @*/ String stringOfEntries(SLNode curr) {
	if (curr == null) {
	    return "";
	}
	// Get string representation of entry. (Note the following works even
	// if the entry is null.)
	String entryAsString = curr.getEntry() + "";

	if (curr.getNextNode() == null
	    // the following disjunct prevents infinite recursion
	    || curr.getNextNode() == this) {
	    return entryAsString;
	}
	return entryAsString + ", " + stringOfEntries(curr.getNextNode());
    }
    protected SLNode() {
	entry_ = null;
	nextNode_ = null;
    }
    protected SLNode(Object ent, SLNode nxtNode) {
	entry_ = ent;
	nextNode_ = nxtNode;
    }
}

