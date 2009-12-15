// @(#)$Id: PriorityQueueUser.java,v 1.10 2007/11/04 20:15:29 leavens Exp $

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
//@ refine "PriorityQueueUser.jml-refined";

public interface PriorityQueueUser {

 /*@ also
   @   public normal_behavior
   @     ensures \result <==>
   @       (\exists QueueEntry e; entries.has(e);
   @                              e.obj == argObj);
   @*/
 /*@ pure @*/ boolean contains(Object argObj);

 /*@ also
   @   public normal_behavior
   @     requires !entries.isEmpty();
   @     ensures
   @       (\exists QueueEntry r;
   @           entries.has(r) && \result == r.obj;
   @           (\forall QueueEntry o;
   @               entries.has(o) && !(r.equals(o));
   @               r.priorityLevel >= o.priorityLevel
   @               && (r.priorityLevel == o.priorityLevel
   @                   ==> r.timeStamp < o.timeStamp) ) );
   @ also
   @   public exceptional_behavior
   @     requires entries.isEmpty();
   @     signals_only PQException;
   @*/
 /*@ pure @*/ Object next() throws PQException;

 /*@ also
   @   public normal_behavior
   @     requires contains(argObj);
   @     assignable entries;
   @     ensures (\exists QueueEntry e;
   @         \old(entries.has(e)) && e.obj == argObj;
   @         entries.equals(\old(entries.remove(e))));
   @ also
   @   public normal_behavior
   @     requires !contains(argObj);
   @     assignable \nothing;
   @     ensures \not_modified(entries);
   @*/
 void remove(Object argObj);

 /*@ also
   @   public normal_behavior
   @     ensures \result <==> entries.isEmpty();
   @*/
 /*@ pure @*/ boolean isEmpty();
}
