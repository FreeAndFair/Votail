// @(#)$Id: Directory.java,v 1.8 2007/04/10 06:19:27 leavens Exp $

// Copyright (C) 2001 Iowa State University

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


package org.jmlspecs.samples.dirobserver;

//@ model import org.jmlspecs.models.JMLString;
//@ model import org.jmlspecs.models.JMLObjectSetEnumerator;

/** Directories that can be both read and written. */
public interface Directory extends RODirectory {

  /** Add a mapping from the given string 
   *  to the given file to this directory.
   */
  /*@ public model_program {
    @   normal_behavior
    @     requires !in_notifier && n != null && n != "" && f != null;
    @     assignable entries;
    @     ensures entries != null
    @        && entries.equals(\old(entries.extend(
    @                                        new JMLString(n), f)));
    @
    @   maintaining !in_notifier && n != null && n != "" && f != null
    @               && e != null;
    @   decreasing e.uniteratedElems.size();
    @   for (JMLObjectSetEnumerator e = listeners.elements();
    @        e.hasMoreElements(); ) {
    @     set in_notifier = true;
    @     ((DirObserver)e.nextElement()).addNotification(this, n);
    @     set in_notifier = false;
    @   }
    @ }
    @*/
  public void addEntry(String n, File f);

  /** Remove the entry with the given name from this directory. */
  /*@ public model_program {
    @   normal_behavior
    @     requires !in_notifier && n != null && n != "";
    @     assignable entries;
    @     ensures entries != null
    @        && entries.equals
    @               (\old(entries.removeDomainElement(
    @                                             new JMLString(n))));
    @
    @   maintaining !in_notifier && n != null && n != "" && e != null;
    @   decreasing e.uniteratedElems.size();
    @   for (JMLObjectSetEnumerator e = listeners.elements();
    @        e.hasMoreElements(); ) {
    @     set in_notifier = true;
    @     ((DirObserver)e.nextElement()).removeNotification(this, n);
    @     set in_notifier = false;
    @   }
    @ }
    @*/
  public void removeEntry(String n);
}
