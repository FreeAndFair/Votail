/**
 * Votail Cuntais - Irish PR-STV ballot counting system
 * 
 * Copyright (c) 2009 Dermot Cochran
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

/**
 * Abstract model of the states and transitions in the election process
 */
package election.util;

/**
 * @author Dermot Cochran
 *
 */
public interface Workflow {
	
	//@ ensures isPossibleState(\result);
	public /*@ pure @*/ int getState();
	
	//@ requires isPossibleState (state);
	//@ requires isTransition (getState(), state);
	//@ ensures getState() == state;
	public void changeState (int state);
	
	public /*@ pure @*/ boolean isPossibleState (int state);
	
	//@ requires isPossibleState (fromState);
	//@ requires isPossibleState (toState);
	public /*@ pure @*/ boolean isTransition (int fromState, int toState);
}
