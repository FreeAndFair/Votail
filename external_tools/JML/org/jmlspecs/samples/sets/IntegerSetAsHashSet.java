// @(#)$Id: IntegerSetAsHashSet.java,v 1.7 2005/12/09 04:20:16 leavens Exp $

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

package org.jmlspecs.samples.sets;

import java.util.*;
//@ model import org.jmlspecs.models.*;

/** A set of integers as a HashSet.
 * @author Katie Becker
 * @author Gary T. Leavens
 */

public class IntegerSetAsHashSet implements IntegerSetInterface {

    private /*@ non_null @*/ HashSet hset;
    //@                      in theSet;
    //@                      maps hset.theSet \into theSet;
    //@ private represents theSet <- abstractValue();

    /** Return the abstract value of this IntegerSetAsHashSet. */

    /*@ 
    private pure model JMLValueSet abstractValue() {
        JMLValueSet ret = new JMLValueSet();
        Iterator iter = hset.iterator();
        while (iter.hasNext()) {
            ret = ret.insert(new JMLInteger((Integer)iter.next()));
        }
        return ret;
    } @*/

    /** Initialize this set to be the empty set. */
    /*@ public normal_behavior
      @   assignable theSet;
      @   ensures theSet != null && theSet.isEmpty();
      @*/
    public IntegerSetAsHashSet() {
        hset = new HashSet();
    }

    public /*@ pure @*/ boolean isMember(int i) {
        return hset.contains(new Integer(i));
    }

    public void insert(int i) {
        hset.add(new Integer(i));
    }

    public void remove(int i) {
        hset.remove(new Integer(i));
    }

    public String toString() {
        return hset.toString();
    }

}
