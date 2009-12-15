// @(#)$Id: RODirectory.java,v 1.8 2005/12/23 17:02:05 chalin Exp $

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

//@ model import org.jmlspecs.models.*;

/** Read-only directories. */
public interface RODirectory extends DirObserverKeeper {
    /** This models the directory's mapping from strings to files. */
    /*@ public model instance JMLValueToObjectMap entries;
      @      public initially entries != null
      @                  && entries.equals(new JMLValueToObjectMap());
      @ public instance invariant entries != null
      @              && (\forall JMLType o; entries.isDefinedAt(o);
      @                           o instanceof JMLString);
      @ public instance invariant
      @             (\forall JMLString s; entries.isDefinedAt(s);
      @                                   entries.apply(s) instanceof File);
      @*/

    /** Return the file with the given name in this directory. */
    /*@ public normal_behavior
      @   requires n != null && !n.equals("");
      @   {|
      @      requires entries.isDefinedAt(new JMLString(n));
      @      assignable \nothing;
      @      ensures \result.equals( (File) entries.apply(new JMLString(n)));
      @    also
      @      requires !entries.isDefinedAt(new JMLString(n));
      @      assignable \nothing;
      @      ensures \result == null;
      @   |}
      @*/
    public File thisFile(String n);

    /*@ also
      @  public normal_behavior
      @  {|
      @     requires !(oth instanceof RODirectory);
      @     ensures \result == false;
      @   also
      @     requires oth instanceof RODirectory;
      @     ensures \result ==
      @        (   entries.equals(((RODirectory)oth).entries)
      @         && listeners.equals(((RODirectory)oth).listeners));
      @  |}
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object oth);
}
