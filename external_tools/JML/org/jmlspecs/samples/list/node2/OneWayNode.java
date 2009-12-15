// @(#) $Id: OneWayNode.java,v 1.9 2007/07/01 02:38:46 chalin Exp $

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

//@ refine "OneWayNode.jml";

public class OneWayNode { // Singly Linked Node

    // data members

    protected /*@ nullable @*/ Object entry_;
    protected /*@ nullable @*/ OneWayNode nextNode_;
    protected /*@ nullable @*/ Link nextLink_;

    // methods

    protected OneWayNode() {
	entry_ = null;
	nextNode_ = null;
	nextLink_ = new Link(null);
    }
    public OneWayNode(/*@ nullable @*/ Object ent) {
	entry_ = ent;
	nextNode_ = null;
	nextLink_ = new Link(null);
    }
    public OneWayNode(/*@ nullable @*/ Object ent,
                      /*@ nullable @*/ OneWayNode nxtNode)
    {
	entry_ = ent;
	nextNode_ = nxtNode;
	nextLink_ = new Link(nxtNode);
    }
    public /*@ pure nullable @*/ Object getEntry() {
	return entry_;
    }
    public void setEntry(/*@ nullable @*/ Object newEntry) {
	entry_ = newEntry;
    }
    public /*@ nullable @*/ OneWayNode getNextNode() {
	return nextNode_;
    }
    public /*@ pure nullable @*/ Link getNextLink() {
	return nextLink_;
    }
    public void insertAfter(/*@ nullable @*/ Object newEntry) {
	nextNode_ = new OneWayNode(newEntry, nextNode_);
	nextLink_ = new Link(nextNode_);
    }
    public void removeNextNode() {
	if (nextNode_ != null) {
	    nextNode_ = nextNode_.getNextNode();
	    nextLink_ = nextLink_.getNext();
	}
    }
    public boolean hasNext() {
	return nextNode_ != null;
    }
    public /*@ pure @*/ String toString() {
	return stringOfEntries(this);
    }

    /** Returns the string concatentation of all nodes following this node up
     * to and excluding the end of the chain or this, which ever is reached
     * first (i.e. this method will terminate even for circular lists).
     */
    protected /*@ pure @*/ String stringOfEntries(
                                     /*@ nullable @*/ OneWayNode curr)
    {
	if (curr == null) {
	    return "";
	}
	// Get string representation of entry. (Note the following works even
	// if the entry is null.)
	String entryAsString = curr.getEntry() + "";

	if (!curr.hasNext()
	    // the following disjunct prevents infinite recursion
	    || curr.getNextNode() == this) {
	    return entryAsString;
	}
	return entryAsString + ", " + stringOfEntries(curr.getNextNode());
    }
}

