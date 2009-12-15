// @(#)$Id: JMLTypeStrategy.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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
 * JMLType. */
public class JMLTypeStrategy 
    extends CloneableObjectAbstractExtensibleStrategyDecorator
{
    /** Initialize this strategy */
    public JMLTypeStrategy() {
        super(new JMLTypeUnextensibleStrategy());
    }

    /** Clone a JMLType object */
    //@ also
    //@ requires elem != null;
    public /*@ pure @*/ Object cloneElement(Object elem) {
        JMLType down = (JMLType) elem;
        return down.clone();
    }

}

/** A strategy for providing test data of type JMLType. */
class JMLTypeUnextensibleStrategy extends CloneableObjectAbstractStrategy
{
    /** Test data of type JMLType */
    protected java.lang.Object[] addData() {
        return new org.jmlspecs.models.JMLType[] {
            null,
            new JMLValueSet(),
            new JMLValueSet(new JMLShort((short)3)),
            new JMLValueSet(new JMLShort((short)3))
            .insert(new JMLShort((short)2)),
            new JMLNegativeInfinity(),
            new JMLValueToValueMap(new JMLShort((short)3),
                                   new JMLShort((short)4))
            .add(new JMLShort((short)2), new JMLShort((short)1)),

        };
    }

    /** Clone a JMLType object */
    //@ also
    //@ requires elem != null;
    protected Object cloneElement(java.lang.Object elem) {
        JMLType down = (JMLType) elem;
        return down.clone();
    }
}
