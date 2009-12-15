// @(#) $Id: E_SLList.java,v 1.4 2005/12/24 21:20:31 chalin Exp $

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

//@ refine "E_SLList.jml";

import org.jmlspecs.samples.list.list1.node.SLNode;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class E_SLList extends SLList { // Singly Linked List

    // data members
    protected int length_;
    protected int log_;

    public E_SLList() {
	super();
	length_ = 0;
	log_ = 0;
    }
    // accessors
    // ---------
    public /*@ pure @*/ int length() {
	return length_;
    }
    public /*@ pure @*/ boolean isEmpty() {
	return length_ == 0;
    }

    // to allow multiple iterations over the same list
    // -----------------------------------------------
    public ListIterator createIterator() {
	return(new ListIterator(this));
    }

    // methods for changing the list
    // -----------------------------
    public void removeEntry() {
	super.removeEntry();
	length_ --;
	log_++;
    }
    public void insertAfterCursor(Object newEntry) {
	super.insertAfterCursor(newEntry);
	length_ ++;
	log_++;
    }
    public void insertBeforeCursor(Object newEntry) {

	decreaseCursor();

	// link previous Node to new Node
	insertAfterCursor(newEntry);

	// move the cursor forward to the original Node
	incrementCursor();
	incrementCursor();
	log_++;
    }

    public void replaceEntry(Object newEntry) {
	super.replaceEntry(newEntry);
	log_++;
    }
    public void append(Object newEntry) {
	lastEntry();
	insertAfterCursor(newEntry);
	incrementCursor();
	log_++;
    }
    public void removeAllEntries() {
	firstEntry();
	while (!isOffEnd()) {
	    removeEntry();
	    incrementCursor();
	}
	log_++;
    }
    public /*@ non_null @*/ Object clone() {
	E_SLList result = new E_SLList( theListNode_, length_ );
	return result;
    }

    // ***********************************************************
    // protected methods

    protected void lastEntry() {
	if (isOffEnd()) {
	    decreaseCursor();
	} else {

	    SLNode lastNode = cursorNode_;

	    while (!isOffEnd()) {
		lastNode = cursorNode_;
		incrementCursor();
	    }
	    cursorNode_ = lastNode;
	}
    }

    protected E_SLList(E_SLList othLst) {
	super(othLst);
	length_ = othLst.length_;
	log_ = othLst.log_;
	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!
	firstEntry();
    }
    protected E_SLList(SLNode listNode, int len) {
	//	super(listNode);
	theListNode_ = (SLNode)listNode.clone();
	length_ = len;
	log_ = 0;
	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!
	firstEntry();
    }
}
