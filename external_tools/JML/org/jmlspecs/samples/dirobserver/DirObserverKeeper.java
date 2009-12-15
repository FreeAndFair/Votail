// @(#)$Id: DirObserverKeeper.java,v 1.4 2004/11/22 04:55:17 leavens Exp $

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

import org.jmlspecs.models.*;

/** An object that keeps directory observers (i.e., a subject). */
public interface DirObserverKeeper extends JMLType {
    
    /** Is a notification callback running? */
    /*@ public ghost instance boolean in_notifier;
      @ public initially !in_notifier;
      @*/

    /** The set of observers. */
    /*@ public model instance JMLObjectSet listeners;
      @ public instance invariant listeners != null;
      @*/

    /** Is a notifier callback running? */
    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == in_notifier;
      @*/
    /*@ pure @*/ boolean inNotifier();

    /** Add a listener to the set of listeners. */
    /*@ public normal_behavior
      @   requires o != null;
      @   assignable listeners;
      @   ensures listeners.equals(\old(listeners.insert(o)));
      @*/
    void register(DirObserver o);

    /** Take a listener out of the set of listeners. */
    /*@ public normal_behavior
      @   requires o != null;
      @   assignable listeners;
      @   ensures listeners.equals(\old(listeners.remove(o)));
      @*/
    void unregister(DirObserver o);
}
