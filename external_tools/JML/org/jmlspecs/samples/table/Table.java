// @(#)$Id: Table.java,v 1.6 2005/07/08 18:13:39 leavens Exp $

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


package org.jmlspecs.samples.table;

import org.jmlspecs.models.*;

/** Tables are finite maps from indexes to values.
 * @author Gary T. Leavens
 * @author Albert L. Baker
 */
public interface Table {

    /** The model of the entries (rows) in the table. */
    /*@ public model instance JMLValueSet entries;
      @ public initially entries != null && entries.isEmpty();
      @*/

    /*@ public instance invariant entries != null
      @   && (\forall JMLType e; entries.has(e); e instanceof Entry);
      @*/

    /*@ public instance invariant
      @   (\forall Entry e1; entries.has(e1);
      @     (\forall Entry e2; entries.has(e2) && !(e1.equals(e2));
      @       !(e1.index.equals(e2.index)) ) ); 
      @*/

    /** Is the given index used in the table? */
    /*@ public normal_behavior
      @    requires d != null;
      @    ensures \result <==>
      @      (\exists Entry e; entries.has(e) && e != null; e.index.equals(d));
      @*/
    /*@ pure @*/ boolean isUsedIndex(JMLType d);

    /** Add the given entry to this table. */
    /*@ public normal_behavior
      @    requires e != null && !isUsedIndex(e.index);
      @    assignable entries;
      @    ensures entries.equals(\old(entries.insert(e)));
      @*/
    void addEntry(Entry e);
 
    /** Take out the given entry from this table. */
    /*@ public normal_behavior
      @    requires d != null;
      @    assignable entries;
      @    ensures entries.equals(
      @              new JMLValueSet { Entry e | 
      @                                  \old(entries).has(e)
      @                                && e != null
      @                                && !(e.index.equals(d)) } );
      @*/
    void removeEntry(JMLType d);
 
    /** Return the value at the given index. */
    /*@ public normal_behavior
      @    requires isUsedIndex(d);
      @    assignable entries;
      @    ensures \fresh(\result)
      @      && (\exists Entry e; entries.has(e);
      @             e.index.equals(d) && \result.equals(e.value));
      @*/
    JMLType mapTo(JMLType d);
}
