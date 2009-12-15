// @(#) $Id: DLList.java,v 1.7 2006/01/04 02:09:35 leavens Exp $

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

package org.jmlspecs.samples.list.list1;

//@ refine "DLList.jml";

import org.jmlspecs.samples.list.list1.node.SLNode;
import org.jmlspecs.samples.list.list1.node.DLNode;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class DLList extends E_SLList { // Doubly Linked List

    final protected DLNode lastNode_;

    public DLList() {
	theListNode_ = new DLNode(null);
	length_ = 0;

	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!
	cursorNode_ = theListNode_;
	theListNode_.insertAfter(null);
	lastNode_ = (DLNode) theListNode_.getNextNode();

	firstEntry();
    }
    // iteration methods
    // -----------------
    public void firstEntry() {
	// The first node is a sentinel so the first entry is in the 2nd node
	cursorNode_ = theListNode_.getNextNode();
    }
    public /*@ pure @*/ boolean isOffEnd() {
	return cursorNode_ == lastNode_;
    }

    public void incrementCursor() {
	if (isOffEnd()) {
	    // System.err.println("Error in `DLList.incrementCursor()': No more List entries");
	    throw new IllegalStateException("Error in `DLList.incrementCursor()': No more List entries");
	}
	cursorNode_ = cursorNode_.getNextNode();
    }

    /*@ non_null @*/ public Object getEntry() {
	if (isOffEnd()) {
	    // The following line is not pure
	    //System.err.println("Error in `DLList.getEntry': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `DLList.getEntry': cursorNode_ is invalid");
	}
	return(cursorNode_.getEntry());
    }

    // NEW iteration methods (for doubly linked list)
    // ---------------------
    public void decrementCursor() {
	if (isOffFront()) {
	    // System.err.println("Error in `DLList.decrementCursor': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `DLList.decrementCursor': cursorNode_ is invalid");
	}
	cursorNode_ = ((DLNode)cursorNode_).getPrevNode();
	// super.decreaseCursor();
    }
    public void lastEntry() {
	// lastNode_ points to sentinel node at end of list.
	// So the node previous to the last sentinel node is the last node.

	cursorNode_ = lastNode_;
	decrementCursor();
    }
    public void removeEntry() {
	if (isOffEnd() || isOffFront()) {
	    // System.err.println("Error in `DLList.removeEntry': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `DLList.removeEntry': cursorNode_ is invalid");
	}

	DLNode prev1 = ((DLNode)cursorNode_).getPrevNode();

	// link the previous node to the next node
	// link the next node back to the previous node
	prev1.removeNextNode();

	cursorNode_ = prev1;
	length_ --;
	log_++;
    }
    public void insertAfterCursor(Object newEntry) {
	DLNode origCursor = (DLNode)cursorNode_;

	if (!isOffEnd()) {
	    incrementCursor();
	}

	insertBeforeCursor(newEntry);
	cursorNode_ = origCursor;
    }
    public void insertBeforeCursor(Object newEntry) {
	DLNode origCursor = (DLNode)cursorNode_;

	if (isOffFront()) {
	    incrementCursor();
	} 

	((DLNode)cursorNode_).insertBefore(newEntry);

	cursorNode_ = origCursor;
	log_++;
	length_ ++;
    }
    public /*@ non_null @*/ Object clone() {
	DLList result = new DLList( (DLNode) theListNode_.clone(),
				    length_ );
	return result;
    }
    public /*@ non_null @*/ String toString() {
	String str = "<";
	if (isOffEnd()) {
	    if (theListNode_.getNextNode() != null) {
		str += theListNode_.getNextNode().toString();
	    }
	    str += " || ";
	} else {
	    str += cursorNode_.toString();
	}
	str += ">";
	return str;
    }

    // ***********************************************************
    // protected methods

    protected DLList(DLList othLst) {
	theListNode_ = (DLNode) othLst.theListNode_;
	length_ = othLst.length_;
	log_ = othLst.log_;
	lastNode_ = othLst.lastNode_;

	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!
	cursorNode_ = theListNode_;

	firstEntry();
    }

    protected DLList(DLNode listNode, int len) {
	theListNode_ = listNode;
	length_ = len;
	log_ = 0;
	SLNode currNode = listNode;
	while (currNode.getNextNode() != null) {
	    currNode = currNode.getNextNode();
	}
	lastNode_ = (DLNode) currNode;

	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!
	cursorNode_ = theListNode_;
	firstEntry();
    }

}
