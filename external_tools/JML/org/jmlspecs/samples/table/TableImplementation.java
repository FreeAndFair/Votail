// @(#)$Id: TableImplementation.java,v 1.7 2005/07/08 18:13:39 leavens Exp $

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

import java.util.Enumeration;
import java.util.Hashtable;
import org.jmlspecs.models.JMLType;

//@ model import org.jmlspecs.models.JMLValueSet;

/** An implementation of the Table interface.
 * @author Katie Becker
 * @author Gary T. Leavens
 */
public class TableImplementation implements Table {

    /** The representation of this Table. */
    private /*@ non_null @*/ Hashtable table;
    //@                          in entries;
    //@                          maps table.theMap \into entries;
    //@ private represents entries <- abstractValue();

    /** Return the set of entries that are, abstractly, in this Table. */
    /*@ ensures \result != null;
    public model pure JMLValueSet abstractValue() {
        JMLValueSet ret = new JMLValueSet();
        Enumeration tableEnum = table.keys();
        while (tableEnum.hasMoreElements()) {
            Object o = tableEnum.nextElement();
            JMLType index = (JMLType)o;
            JMLType value = (JMLType)table.get(index);
            ret = ret.insert(new EntryImplementation(index, value));       
        }
        return ret;
    } @*/

    /** Initialize this Table to contain the empty set of entries. */
    /*@ public normal_behavior
      @   assignable entries;
      @    ensures entries != null && entries.isEmpty();
      @ implies_that
      @   private normal_behavior
      @     assignable entries, table;
      @     ensures table != null;
      @*/
    public TableImplementation() {
        table = new Hashtable();
    }

    public /*@ pure @*/ boolean isUsedIndex(JMLType d) {
        return table.containsKey(d);
    }

    public void addEntry(Entry e) {
        table.put(e.getIndex(), e.getValue());
    }

    public void removeEntry(JMLType d) {
        table.remove(d);
    }
 
    public JMLType mapTo(JMLType d){
        return (JMLType)table.get(d);
    }
 
    public String toString() {
        return table.toString();
    }
}  


