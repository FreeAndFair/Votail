// @(#) $Id: Iterator.java,v 1.4 2005/12/24 21:20:31 chalin Exp $

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

// Author: Clyde Ruby

package org.jmlspecs.samples.list.iterator;

//@ model import org.jmlspecs.models.JMLObjectBag;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public interface Iterator { 

  //@ public model instance JMLObjectBag uniteratedElems;
  //@ public model instance nullable Object currElem;
  //@ public model instance boolean unchanged;

  /*@ public instance invariant uniteratedElems.has(currElem) 
    @                           || currElem == null;
    @*/

  /*@  public normal_behavior
    @    requires unchanged && !isDone();
    @    {|
    @      requires uniteratedElems.int_size() > 1;
    @      assignable uniteratedElems, currElem;
    @      ensures uniteratedElems.equals(
    @                   \old(uniteratedElems).remove(\old(currElem)) )
    @         && uniteratedElems.has(currElem);
    @      ensures_redundantly 
    @         uniteratedElems.int_size() == \old(uniteratedElems).int_size() - 1;
    @    also
    @      requires uniteratedElems.int_size() == 1;
    @      assignable uniteratedElems;
    @      ensures uniteratedElems.isEmpty();
    @    |}
    @*/
  public void next();

  /*@  public normal_behavior
    @    requires unchanged;
    @    assignable \nothing;
    @    ensures \result == uniteratedElems.isEmpty();
    @*/
  public /*@ pure @*/ boolean isDone();

  /*@  public normal_behavior
    @    requires unchanged && !isDone();
    @    assignable \nothing;
    @    ensures \result == currElem;
    @*/
  public /*@ pure nullable @*/ Object currentItem();
}


