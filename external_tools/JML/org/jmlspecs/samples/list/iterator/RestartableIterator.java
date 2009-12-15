// @(#) $Id: RestartableIterator.java,v 1.4 2005/12/24 21:20:31 chalin Exp $

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

public interface RestartableIterator extends Iterator {

    /*@ public model instance JMLObjectBag iteratedElems;
      @                                    in uniteratedElems;
      @*/

  /*@
    @  public normal_behavior
    @    requires unchanged;
    @    assignable iteratedElems, currElem, uniteratedElems;
    @    ensures uniteratedElems.equals(
    @ 		   \old(iteratedElems).union(\old(uniteratedElems)))
    @         && iteratedElems.isEmpty();
    @*/
  public void first();

  /*@
    @ also
    @  public normal_behavior
    @    requires unchanged && !isDone();
    @    assignable iteratedElems;
    @    ensures iteratedElems.equals(
    @ 		   \old(iteratedElems).insert(\old(currElem)));
    @*/
  public void next();

  /*@
    @ also
    @  public normal_behavior
    @    requires unchanged;
    @    assignable \nothing;
    @    ensures \result == uniteratedElems.isEmpty();
    @*/
  public /*@ pure @*/ boolean isDone();

  /*@
    @ also
    @  public normal_behavior
    @    requires unchanged && !isDone();
    @    assignable \nothing;
    @    ensures \result == currElem;
    @*/
  public /*@ pure nullable @*/ Object currentItem();
}

