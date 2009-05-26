/**
 * Votail Cuntais - Irish PR-STV ballot counting system
 * 
 * Copyright (c) 2005-2009 Dermot Cochran, Joseph R. Kiniry and Patrick E. Tierney
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

package election.tally;

/** Data transfer structure for set of all valid votes */
//@ refine "BallotBox.java-refined";
public class BallotBox {
	
/**
 * List of valid ballot papers
 * 
 * @constraint No two ballots IDs in a ballot box are the same
 */
/*@ public invariant (\forall int i, j;
  @   0 <= i && i <numberOfBallots &&
  @   0 <= j && j <numberOfBallots &&
  @   i != j;
  @   ballots[i].ballotID != ballots[j].ballotID);
  @*/	
	protected /*@ spec_public non_null @*/ Ballot[] ballots;
	
/**
 * @return the number of ballots in this ballot box
 */	
/*@ also 
  @ public normal_behavior
  @ ensures 0 <= \result;
  @*/
   public /*@ pure @*/ long size(){
		return numberOfBallots;
	}
	
//@ public invariant 0 <= numberOfBallots;
//@ public initially numberOfBallots == 0;
//@ public constraint numberOfBallots >= \old(numberOfBallots);
	/**
	 * The total number of ballots in this ballot box.
	 */
	public int numberOfBallots;
	
	/**
	 * Create an empty ballot box.
	 */
	public BallotBox(){
		numberOfBallots = 0;
		ballots = new Ballot[numberOfBallots];
	}

	/**
	 * Get the full set of ballots cast.
	 * 
	 * @return The full set of ballots.
	 */
	/*@ public normal_behavior
	  @   ensures ballots == \result;
	  @*/
	public /*@ pure non_null @*/ Ballot[] getBallots() {
 		return ballots;
	}
}