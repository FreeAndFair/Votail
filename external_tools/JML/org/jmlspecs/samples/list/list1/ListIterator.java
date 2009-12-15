// @(#) $Id: ListIterator.java,v 1.8 2005/12/24 21:20:31 chalin Exp $

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

//@ refine "ListIterator.jml-refined";

//@ model import org.jmlspecs.models.JMLObjectBag;
import org.jmlspecs.samples.list.iterator.Iterator;
import org.jmlspecs.samples.list.iterator.RestartableIterator;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class ListIterator implements RestartableIterator {

    // data members
    protected E_SLList listRef_;
    /*@                in listPtr;
      @                maps listRef_.cursor \into currIndex;
      @                maps listRef_.changeLog \into unchanged;
      @*/

    protected int origLog_;
    //@           in origChgLog;

    //@ protected represents listPtr <- listRef_;
    //@ protected represents currIndex <- listRef_.cursor;
    //@ protected represents origChgLog <- origLog_;

    /*@ protected represents currElem <- 
      @     (!listRef_.isOffFront() && !listRef_.isOffEnd())
      @   ? currentItem()
      @   : null;
      @*/

    /*@ protected represents iteratedElems <-
      @            JMLObjectBag.convertFrom(
      @                listRef_.theList.prefix(currIndex) );
      @*/

    /*@ protected represents uniteratedElems <-
      @            JMLObjectBag.convertFrom(
      @                listRef_.theList.removePrefix(currIndex) );
      @*/

    //@ protected represents currIndex <- listRef_.cursor;
    //@ protected represents unchanged <- (listRef_.changeLog == origChgLog);

  /*@ also
    @ protected normal_behavior
    @   requires lst != null;
    @   assignable listRef_, listRef_.cursor, origLog_;
    @   ensures listRef_.cursor == 0
    @         && listRef_.theList.equals(lst.theList)
    @         && \fresh(listRef_);
    @*/
    public ListIterator(E_SLList lst) {
	origLog_ = lst.log_;
	listRef_ = (E_SLList)lst.clone();
	listRef_.firstEntry();
    }

    // don't allow the default constructor
    private ListIterator() {
    }

  /*@ also
    @ protected normal_behavior
    @   assignable listRef_.cursor;
    @   ensures listRef_.cursor == 0;
    @*/
    public void first() {
	listRef_.firstEntry();
    }

  /*@ also
    @ protected normal_behavior
    @   requires !listRef_.isOffEnd();
    @   assignable listRef_.cursor;
    @   ensures listRef_.cursor == \pre(listRef_.cursor + 1);
    @*/
    public void next() {
	listRef_.incrementCursor();
    }

  /*@ also
    @ protected normal_behavior 
    @   assignable \nothing;
    @   ensures \result 
    @       == (listRef_.cursor == listRef_.theList.int_length());
    @*/
    public boolean isDone() {
	return(listRef_.isOffEnd());
    }

  /*@ also
    @ protected normal_behavior 
    @   requires !listRef_.isOffFront() && !listRef_.isOffEnd();
    @   requires_redundantly listRef_.length() > 0;
    @   assignable \nothing;
    @   ensures \result == listRef_.theList.itemAt(listRef_.cursor);
    @*/
    public Object currentItem() {
	return(listRef_.getEntry());
    }
    public /*@ non_null @*/ String toString() {
	return listRef_.toString();
    }

}

