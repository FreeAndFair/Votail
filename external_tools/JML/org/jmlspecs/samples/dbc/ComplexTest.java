// @(#)$Id: ComplexTest.java,v 1.2 2003/02/08 03:22:56 leavens Exp $

// Copyright (C) 2003 Iowa State University

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


package org.jmlspecs.samples.dbc;

import junit.framework.TestCase;

/** Test for the complex number types. */
public strictfp class ComplexTest extends TestCase {

    /** Constructor for ComplexTest.
     * @param name
     */
    public ComplexTest(String name) {
        super(name);
    }

    public static void main(String[] args) {
        junit.textui.TestRunner.run(ComplexTest.class);
    }

    private static final double tolerance = 0.005;
    private Complex[] receivers;

    /** Check that either the numbers are equal, or
     *   StrictMath.abs(d1-d2)
     *    <= StrictMath.max(StrictMath.abs(d1),
     *                      StrictMath.abs(d2))*tolerance.
     */
    protected void approximatelyEquals(double d1, double d2) {
        if (d1 == d2) {
            // handles cases where both are zero or infinity
            return;
        } else {
            assertEquals(d1, d2,
                         StrictMath.max(StrictMath.abs(d1),
                                        StrictMath.abs(d2))*tolerance);
        }
    }

    /** Check that either the numbers are equal, or
     *   StrictMath.abs(d1-d2)
     *      <= StrictMath.max(StrictMath.abs(d1),
     *                        StrictMath.abs(d2))*tolerance.
     */
    protected void approximatelyEquals(String msg, double d1, double d2) {
        if (d1 == d2) {
            // handles cases where both are zero or infinity
            return;
        } else {
            assertEquals(msg, d1, d2,
                         StrictMath.max(StrictMath.abs(d1),
                                        StrictMath.abs(d2))*tolerance);
        }
    }

    /** Initalize the receivers array. */
    protected void setUp() throws Exception {
        if (receivers == null) {
            receivers =
                new Complex[] {
                    new Rectangular(0.0, 0.0),
                    new Rectangular(2.0, 0.0),
                    new Rectangular(2.1, 3.4),
                    new Rectangular(-10.0, 75.2),
                    new Rectangular(-57.34, -0.1e-10),
                    new Polar(0.0, 0.0),
                    new Polar(2.1, StrictMath.PI / 3),
                    new Polar(7.5, StrictMath.PI - 0.02),
                    new Polar(-10.6, 3 * StrictMath.PI / 2),
                    };
        }
    }

    /** Test the method Polar.standardizeAngle. */
    public void testStandardizeAngle() {
        approximatelyEquals(0.0, Polar.standardizeAngle(0.0));
        approximatelyEquals(3.0, Polar.standardizeAngle(3.0));
        approximatelyEquals(-0.5*StrictMath.PI,
                            Polar.standardizeAngle(1.5*StrictMath.PI));
        approximatelyEquals(0.5*StrictMath.PI,
                            Polar.standardizeAngle(-1.5*StrictMath.PI));
        approximatelyEquals(0.5*StrictMath.PI,
                            Polar.standardizeAngle(6.5*StrictMath.PI));
        approximatelyEquals(0.5*StrictMath.PI,
                            Polar.standardizeAngle(-7.5*StrictMath.PI));
    }

    /** Test the method realPart. */
    public void testRealPart() {
        for (int i = 0; i < receivers.length; i++) {
            approximatelyEquals(
                receivers[i].magnitude()
                * StrictMath.cos(receivers[i].angle()), 
                receivers[i].realPart());
        }
    }

    /** Test the method imaginaryPart. */
    public void testImaginaryPart() {
        for (int i = 0; i < receivers.length; i++) {
            approximatelyEquals(
                receivers[i].magnitude()
                * StrictMath.sin(receivers[i].angle()), 
                receivers[i].imaginaryPart());
        }
    }

    /** Test the method magnitude. */
    public void testMagnitude() {
        for (int i = 0; i < receivers.length; i++) {
            approximatelyEquals(
                StrictMath.sqrt(
                    receivers[i].realPart() * receivers[i].realPart()
                        + receivers[i].imaginaryPart()
                            * receivers[i].imaginaryPart()), 
                receivers[i].magnitude());
        }
    }

    /** Test the method angle. */
    public void testAngle() {
        for (int i = 0; i < receivers.length; i++) {
            approximatelyEquals(
                "Angle not right for " + receivers[i],
                StrictMath.atan2(
                    receivers[i].imaginaryPart(),
                    receivers[i].realPart()
                    ),
                receivers[i].angle());
        }
    }

    /** Test the method add. */
    public void testAdd() {
        for (int i = 0; i < receivers.length; i++) {
            for (int j = 0; j < receivers.length; j++) {
                approximatelyEquals(
                    "Add real part not right for " + receivers[i]
                    + " and " + receivers[j],
                    receivers[i].realPart() + receivers[j].realPart(),
                    receivers[i].add(receivers[j]).realPart());
                approximatelyEquals(
                    receivers[i].imaginaryPart()
                    + receivers[j].imaginaryPart(),
                    receivers[i].add(receivers[j]).imaginaryPart());
            }
        }
    }

    /** Test the method sub. */
    public void testSub() {
        for (int i = 0; i < receivers.length; i++) {
            for (int j = 0; j < receivers.length; j++) {
                approximatelyEquals(
                    "Sub real part not right for " + receivers[i]
                    + " and " + receivers[j],
                    receivers[i].realPart() - receivers[j].realPart(),
                    receivers[i].sub(receivers[j]).realPart());
                approximatelyEquals(
                    receivers[i].imaginaryPart()
                    - receivers[j].imaginaryPart(),
                    receivers[i].sub(receivers[j]).imaginaryPart());
            }
        }
    }

    /** Test the method mul. */
    public void testMul() {
        for (int i = 0; i < receivers.length; i++) {
            for (int j = 0; j < receivers.length; j++) {
                approximatelyEquals(
                    receivers[i].magnitude() * receivers[j].magnitude(), 
                    receivers[i].mul(receivers[j]).magnitude());
                approximatelyEquals(
                    Polar.standardizeAngle(receivers[i].angle()
                                           + receivers[j].angle()), 
                    receivers[i].mul(receivers[j]).angle());
            }
        }
    }

    /** Test the method div. */
    public void testDiv() {
        for (int i = 0; i < receivers.length; i++) {
            for (int j = 0; j < receivers.length; j++) {
                if (receivers[j].magnitude() != 0) {
                    approximatelyEquals(
                        receivers[i].magnitude() / receivers[j].magnitude(), 
                        receivers[i].div(receivers[j]).magnitude());
                    approximatelyEquals(
                        Polar.standardizeAngle(receivers[i].angle()
                                               - receivers[j].angle()), 
                        receivers[i].div(receivers[j]).angle());
                }
            }
        }
    }

    /** Test the method equals. */
    public void testEquals() {
        for (int i = 0; i < receivers.length; i++) {
            assertFalse(receivers[i].equals(null));
            assertFalse(receivers[i].equals(new Double(2.0)));
            for (int j = 0; j < receivers.length; j++) {
                assertEquals(
                    i == j
                        || (receivers[i].realPart() == receivers[j].realPart()
                            && receivers[i].imaginaryPart()
                                == receivers[j].imaginaryPart()),
                    receivers[i].equals(receivers[j]));
            }
        }
    }

    /** Test the method hashCode. */
    public void testHashCode() {
        for (int i = 0; i < receivers.length; i++) {
            // the following tests that we don't get exceptions...
            receivers[i].hashCode();

            // the following tests that equal objects have equal hashcodes
            for (int j = i+1; j < receivers.length; j++) {
                if (receivers[i].equals(receivers[j])) {
                    assertTrue(receivers[i].hashCode()
                               == receivers[j].hashCode());
                }
            }
        }
    }

    /** Test the method toString. */
    public void testToString() {
        for (int i = 0; i < receivers.length; i++) {
            assertTrue(receivers[i].toString() != null);
        }
    }

}
