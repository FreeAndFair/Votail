// @(#)$Id: LimitedTestSuite.java,v 1.6 2005/07/07 21:03:04 leavens Exp $

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

import junit.framework.TestSuite;
import junit.framework.Test;

/** A kind of test suite that only allows the first n tests to be
 * added, and ignores the rest.
 * @see junit.framework.TestSuite
 * @author Gary T. Leavens
 */
public class LimitedTestSuite extends TestSuite {

    protected /*@ spec_public @*/ int limit;

    /** Initialize this LimitedTestSuite to have the given limit. */
    //@ requires n >= 0;
    //@ assignable limit;
    //@ ensures limit == n;
    public LimitedTestSuite(int n) {
        limit = n;
    }

    /** Initialize this LimitedTestSuite to have the given limit. */
    //@ requires n >= 0;
    //@ assignable limit, objectState;
    //@ ensures limit == n;
    public LimitedTestSuite(String name, int n) {
        super(name);
        limit = n;
    }

    /** Add a test to this test suite, or throw a
     * TestSuiteFullException if this test suite is already full. */
    /*@ also
      @   public behavior
      @    assignable objectState;
      @    signals_only TestSuiteFullException;
      @    signals (TestSuiteFullException) testCount() >= limit; 
      @*/
    public void addTest(Test test) {
        if (testCount() < limit) {
            super.addTest(test);
        } else {
            throw new TestSuiteFullException();
        }
    }
}
