// @(#) $Id: SLList.java,v 1.11 2007/07/01 02:38:45 chalin Exp $

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

//@ refine "SLList.jml";

import org.jmlspecs.samples.list.list1.node.SLNode;

//@ model import org.jmlspecs.models.JMLObjectSequence;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class SLList { // Singly Linked List

    // data members

    protected /*@non_null*/ SLNode theListNode_;

    // used for inserting and iteration through the List 
    protected SLNode cursorNode_;

    public SLList() {
	theListNode_ = new SLNode(null);
	cursorNode_ = null;
    }

    // iteration methods
    // -----------------

    public void firstEntry() {
	// The first node is a sentinel so the first entry is in the 2nd node
	cursorNode_ = theListNode_.getNextNode();
    }
    public void incrementCursor() {
	if (isOffEnd()) {
	    // System.err.println("Error in `SLList.incrementCursor()': No more List entries"
	    //	       + "List is " + this.toString() );
	    throw new IllegalStateException("Error in `SLList.OneWayList.incrementCursor()': No more List entries\n"
					    + "List is " + this.toString() );
	}
	cursorNode_ = cursorNode_.getNextNode();
    }
    public /*@ pure @*/ boolean isOffFront() {
	return cursorNode_ == theListNode_;
    }
    public /*@ pure @*/ boolean isOffEnd() {
	return cursorNode_ == null;
    }
    public /*@ pure @*/ Object getEntry() {
	if (isOffEnd() || isOffFront()) {
	    // The following line is not pure
	    //System.err.println("Error in `SLList.getEntry': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `SLList.getEntry': cursorNode_ is invalid");
	}
	return cursorNode_.getEntry();
    }

    // methods for changing the list
    // -----------------------------
    public void removeEntry() {
	if (isOffEnd() || isOffFront()) {
	    // System.err.println("Error in `SLList.removeEntry': cursorNode_ is invalid");
	    // System.err.println("List is " + this.toString());
	    throw new IllegalStateException("Error in `SLList.removeEntry':"
					    + "cursorNode_ is invalid\n"
					    + "List is " + this.toString());
	}

	// link the previous node to the next node
	decreaseCursor();
	cursorNode_.removeNextNode();
    }
    public void replaceEntry(Object newEntry) {
	cursorNode_.setEntry(newEntry);
    }
    public void insertAfterCursor(Object newEntry) {
	if (isOffEnd()) {
	    // System.err.println("Error in `SLList.insertAfterCursor': cursorNode_ is invalid");
	    // System.err.println("Attempting to insert " + newEntry);
	    // System.err.println("into list " + this.toString());
	    throw new IllegalStateException("Error in `SLList.insertAfterCursor':"
					    + " cursorNode_ is invalid\n"
					    + "Attempting to insert " 
					    + newEntry 
					    + "into list " + this.toString() );
	}

	// creat a new Node containing newEntry and insert after cursor
	cursorNode_.insertAfter(newEntry);
    }
    public void insertBeforeCursor(Object newEntry) {
	if (isOffFront()) {
	    // System.err.println("Error in `SLList.insertBeforeCursor': cursorNode_ is invalid");
	    // System.err.println("Attempting to insert " + newEntry);
	    // System.err.println("into list " + this.toString());
	    throw new IllegalStateException("Error in `SLList.insertBeforeCursor':"
					    + " cursorNode_ is invalid\n"
					    + "Attempting to insert " 
					    + newEntry 
					    + "into list " + this.toString() );
	}

	decreaseCursor();

	// link previous Node to new Node
	insertAfterCursor(newEntry);

	// move the cursor forward to the original Node
	incrementCursor();
	incrementCursor();
    }
    public /*@ non_null @*/ Object clone() {
	SLList result = new SLList( theListNode_ );
	return result;
    }
    public /*@ non_null @*/ String toString() {
	String str = "<";
	SLNode curr = theListNode_.getNextNode();
	while (curr != cursorNode_ && curr != null) {
	    str = str + curr.getEntry();
	    curr = curr.getNextNode();
	    if (curr != null && curr.getNextNode() != null) {
		str += ", ";
	    }
	}
	str += " || ";
	while (curr != null) {
	    str = str + curr.getEntry();
	    curr = curr.getNextNode();
	    if (curr != null && curr.getNextNode() != null) {
		str += ", ";
	    }
	}
	str += ">";
	return str;
    }

    // ***********************************************************
    // protected methods

    protected void decreaseCursor() {
	if (isOffFront()) {
	    // System.err.println("Error in `SLList.decreaseCursor': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `SLList.decreaseCursor': cursorNode_ is invalid");
	}
	SLNode origCursor = cursorNode_;

	firstEntry();

	if (cursorNode_ == origCursor) {
	    cursorNode_ = theListNode_;
	} else {
	    while (!isOffEnd() && cursorNode_.getNextNode() != origCursor) {
		incrementCursor();
	    }
	}
    }
    protected SLList(SLList othLst) {
	theListNode_ = (SLNode)othLst.theListNode_.clone();
	firstEntry();
    }
    protected SLList(SLNode listNode) {
	theListNode_ = (SLNode)listNode.clone();
	firstEntry();
    }

}
