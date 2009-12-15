// @(#) $Id: TwoWayNode.java,v 1.10 2007/07/01 02:38:46 chalin Exp $

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

package org.jmlspecs.samples.list.node;

//@ refine "TwoWayNode.jml";

public class TwoWayNode extends OneWayNode { // Doubly Linked Node

    // data members

    protected /*@ nullable @*/ TwoWayNode prevNode_;

    public TwoWayNode() {
	super();
	prevNode_ = null;
    }
    public TwoWayNode(/*@ nullable @*/ Object ent) {
	super(ent);
	prevNode_ = null;
    }
    public void insertAfter(/*@ nullable @*/ Object newEntry) {
	nextNode_ = new TwoWayNode(newEntry, this, (TwoWayNode)nextNode_);
    }
    public void removeNextNode() {
	if (nextNode_ != null) {
	    TwoWayNode nextNextNode = (TwoWayNode) nextNode_.getNextNode();

	    // remove the current links
	    // the next line is needed in case nextNode_ is aliased
	    ((TwoWayNode) nextNode_).linkTo(null);

	    this.linkTo(nextNextNode);
	}
    }
    public /*@ pure nullable @*/ TwoWayNode getPrevNode() {
	return prevNode_;
    }
    public void insertBefore(/*@ nullable @*/ Object newEntry) {
	prevNode_ = new TwoWayNode(newEntry, prevNode_, this);
    }
    public String toString() {
	String str = "";
	str += stringOfPrevEntries(((TwoWayNode)this).getPrevNode());
	str += " || ";
	str += stringOfEntries(this);
	return str;
    }

    /** The first invocation of this method should be with curr ==
     * prevNode_. If this is done, then the string returned will be a
     * concatentation of all nodes prior to this node up to and excluding the
     * end of the chain or this, which ever is reached first (i.e. this method
     * will terminate even for circular lists).
     */
    protected /*@ pure @*/ String stringOfPrevEntries(
                                      /*@ nullable @*/ TwoWayNode curr)
    {
	if (curr == null
	    // the following disjunct prevents infinite recursion
	    || curr == this) {
	    return "";
	}
	return stringOfPrevEntries(curr.getPrevNode())
	    + curr.getEntry() + ", ";
    }
    public Object clone() {
	if (nextNode_ == null) {
	    if (prevNode_ == null) {
		return new TwoWayNode(getEntry());
	    } else {
		return new TwoWayNode(getEntry(), 
				      prevNode_.clonePrevious(), null);
	    }
	} else {
	    if (prevNode_ == null) {
		return new TwoWayNode(getEntry(), null, 
				      ((TwoWayNode)nextNode_).cloneNext());
	    } else {
		return new TwoWayNode(getEntry(), 
				      prevNode_.clonePrevious(), 
				      ((TwoWayNode)nextNode_).cloneNext());
	    }
	}
    }
    protected /*@ pure @*/ TwoWayNode cloneNext() {
	if (nextNode_ == null) {
	    return new TwoWayNode(getEntry());
	} else {
	    return new TwoWayNode(getEntry(), null, 
			      ((TwoWayNode)nextNode_).cloneNext());
	}
    }
    protected /*@ pure @*/ TwoWayNode clonePrevious() {
	if (prevNode_ == null) {
	    return new TwoWayNode(getEntry());
	} else {
	    return new TwoWayNode(getEntry(), prevNode_.clonePrevious(), null);
	}
    }
    private /*@ helper @*/ void linkTo(/*@ nullable @*/ TwoWayNode nxtNode) {
	if (nextNode_ != null) {
	    // needed in case nextNode_ is aliased

	    ((TwoWayNode)nextNode_).prevNode_ = null;
	}
	if (nxtNode != null) {
	    // has to be done here or in a private helper method 
	    // so the invariant holds!
	    nxtNode.prevNode_ = this;
	}
	nextNode_ = nxtNode;
    }
    protected TwoWayNode(/*@ nullable @*/ Object ent,
                         /*@ nullable @*/ TwoWayNode prvNode,
                         /*@ nullable @*/ TwoWayNode nxtNode)
    {
	this(ent);
	if (prvNode != null) {
	    prvNode.linkTo(this);
	}
	if (nxtNode != null) {
	    this.linkTo(nxtNode);
	}
    }
}

