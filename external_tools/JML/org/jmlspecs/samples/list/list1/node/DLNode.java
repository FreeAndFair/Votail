// @(#) $Id: DLNode.java,v 1.7 2005/12/24 21:20:31 chalin Exp $

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

//@ refine "DLNode.jml";

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class DLNode extends SLNode { // Doubly Linked Node

    // data members

    protected DLNode prevNode_;

    public DLNode(Object ent) {
	super(ent);
	prevNode_ = null;
    }

    public void insertAfter(Object newEntry) {
	nextNode_ = new DLNode(newEntry, this, (DLNode)nextNode_);
    }
    public void removeNextNode() {
	if (nextNode_ != null) {
	    DLNode nextNext = (DLNode) nextNode_.getNextNode();

	    // remove the current links
	    // the next two lines are needed in case nextNode_ is aliased
	    ((DLNode)nextNode_).linkTo(null);

	    this.linkTo(nextNext);
	}
    }
    public /*@ pure @*/ DLNode getPrevNode() {
	return prevNode_;
    }
    public void insertBefore(Object newEntry) {
	if (prevNode_ != null) {
	    prevNode_.insertAfter(newEntry);
	} else {
	    prevNode_ = new DLNode(newEntry, null, this);
	}
    }
    public /*@ non_null @*/ Object clone() {
	if (nextNode_ == null) {
	    if (prevNode_ == null) {
		return new DLNode(getEntry());
	    } else {
		return new DLNode(getEntry(), prevNode_.clonePrevious(), null);
	    }
	} else {
	    if (prevNode_ == null) {
		return new DLNode(getEntry(), null, 
				  ((DLNode)nextNode_).cloneNext());
	    } else {
		return new DLNode(getEntry(), 
				  prevNode_.clonePrevious(), 
				  ((DLNode)nextNode_).cloneNext());
	    }
	}
    }
    protected DLNode cloneNext() {
	if (nextNode_ == null) {
	    return new DLNode(getEntry());
	} else {
	    return new DLNode(getEntry(), null, 
			      ((DLNode)nextNode_).cloneNext());
	}
    }
    protected DLNode clonePrevious() {
	if (prevNode_ == null) {
	    return new DLNode(getEntry());
	} else {
	    return new DLNode(getEntry(), prevNode_.clonePrevious(), null);
	}
    }
    protected void linkTo(DLNode nxtNode) {
	if (nextNode_ != null) { // needed in case nextNode_ is aliased
	    ((DLNode)nextNode_).prevNode_ = null;
	}
	if (nxtNode != null) {
	    nxtNode.prevNode_ = this;
	}
	this.nextNode_ = nxtNode;
    }
    protected DLNode(Object ent, DLNode prvNode, DLNode nxtNode) {
	this(ent);
	if (prvNode != null) {
	    prvNode.linkTo(this);
	}
	if (nxtNode != null) {
	    this.linkTo(nxtNode);
	}
    }
}

