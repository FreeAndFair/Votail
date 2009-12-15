// @(#)$Id: JMLCollectionStrategy.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

package org.jmlspecs.jmlunit.strategies;

import org.jmlspecs.models.*;

/** A strategy for generating test data of type
 * JMLCollection. */
public class JMLCollectionStrategy 
    extends NewObjectAbstractExtensibleStrategyDecorator
{
    /** Initialize this strategy */
    public JMLCollectionStrategy() {
        super(new JMLCollectionUnextensibleStrategy());
    }
}

/** A strategy for providing test data of type JMLCollection. This
 * subclasses ImmutableObjectAbstractStrategy because the test data
 * provided are all immutable. */
class JMLCollectionUnextensibleStrategy extends ImmutableObjectAbstractStrategy
{
    /** Test data of type JMLCollection.  These should all be
     * immutable, or the superclass of this class should be
     * changed. */
    protected java.lang.Object[] addData() {
        return new org.jmlspecs.models.JMLCollection[] {
            null,
            new JMLValueSet().insert(new JMLInteger(3)),
            new JMLValueBag().insert(new JMLInteger(3))
            .insert(new JMLInteger(4)).insert(new JMLInteger(3)),
            new JMLValueSequence(new JMLInteger(7))
            .insertFront(new JMLInteger(22)),
        };
    }
}
