// @(#)$Id: QueueEntry.java,v 1.2 2005/12/23 17:02:05 chalin Exp $

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


package org.jmlspecs.samples.jmlkluwer;

//@ refine "QueueEntry.jml-refined";

import org.jmlspecs.models.JMLType;

public /*@ pure @*/ class QueueEntry implements JMLType {

    private /*@ non_null @*/ Object _obj; //@ in obj;
    private int _priorityLevel; //@ in priorityLevel;
    private long _timeStamp; //@ in timeStamp;

    //@ private represents obj <- _obj;
    //@ private represents priorityLevel <- _priorityLevel;
    //@ private represents timeStamp <- _timeStamp;

    /*@ private invariant_redundantly
      @    _priorityLevel >= 0 && _timeStamp >= 0L;
      @*/

    public QueueEntry(Object argObj, int argLevel,
                      long argTimeStamp) {
        _obj = argObj;
        _priorityLevel = argLevel;
        _timeStamp = argTimeStamp;
    }

    public boolean equals(/*@ nullable @*/ Object o) {
        if (!(o instanceof QueueEntry)) {
            return false;
        }

        QueueEntry qe = (QueueEntry)o;
        return qe._obj == _obj
            && qe._priorityLevel == _priorityLevel
            && qe._timeStamp == _timeStamp;
    }

    public /*@ pure @*/ int hashCode() {
        return _obj.hashCode();
    }

    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            // should not happen
            throw new InternalError(e.getMessage());
        }
    }

    public /*@ pure @*/ int getLevel() {
        return _priorityLevel;
    }

    public /*@ pure @*/ Object getObj() {
        return _obj;
    }

    public String toString() {
        return "[obj: " + _obj.toString()
            + ", priorityLevel: " + _priorityLevel
            + ", timeStamp: " + _timeStamp
            + "]";
    }
}
