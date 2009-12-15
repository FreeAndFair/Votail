// @(#)$Id: File.java,v 1.4 2005/12/23 17:02:05 chalin Exp $

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

/** A simplified file class for purposes of this example. */
public class File {

    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object o) {
        if (o == null || !(o instanceof File)) {
            return false;
        }
        return true; // this is a stub only...
    }
}
