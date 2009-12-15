// @(#)$Id: ConstructorFailed.java,v 1.2 2005/07/07 21:03:04 leavens Exp $

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

import junit.framework.*;

/** A class that stores an exception that occured during test suite
 * construction as a JUnit test, and when the test is run makes the
 * problem a failure.
 * @author Gary T. Leavens
 */
public class ConstructorFailed implements Test {

    /** The problem that occurred. */
    private final /*@ spec_public non_null @*/ Throwable cause;

    /** Initialize this object */
    //@ requires ex != null;
    //@ assignable cause;
    //@ ensures cause == ex;
    public ConstructorFailed(Throwable ex) {
        cause = ex;
    }

    // doc comment and specification inherited
    public int countTestCases() {
        return 1;
    }

    /** The failure message for failures raised by this class. */
    private final String failmsg = "Failure during construction of test suite";

    /** Add a failure corresponding to cause to the result object. */
    // specification inherited
    public void run(TestResult result) {
        AssertionFailedError err = new AssertionFailedError(failmsg);
        err.setStackTrace(new StackTraceElement[]{});
        err.initCause(cause);
        result.addFailure(this, err);
    }
}
