/**
 * Votail Cuntais - Irish PR-STV ballot counting system
 * 
 * Copyright (c) 2005 Dermot Cochran and Joseph R. Kiniry
 * Copyright (c) 2006,2007 Dermot Cochran, Joseph R. Kiniry and Patrick E. Tierney
 * Copyright (c) 2008,2009 Dermot Cochran
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
 * List of valid ballot papers.
 */
/*@ public invariant (\forall int i, j;
  @   0 <= i && i < numberOfBallots &&
  @   0 <= j && j < numberOfBallots &&
  @   i != j && ballots[i] != null && ballots[j] != null;
  @   ballots[i].ballotID != ballots[j].ballotID);
  @*/	
	protected /*@ spec_public non_null @*/ Ballot[] ballots;
	
/**
 * Get the number of ballots in this box.
 * 
 * @return the number of ballots in this ballot box
 */	
/*@ also 
  @ public normal_behavior
  @   ensures 0 <= \result;
  @   ensures \result == numberOfBallots;
  @*/
   public /*@ pure @*/ int size(){
		return numberOfBallots;
	}
	
    //@ public invariant 0 <= numberOfBallots;
    //@ public initially numberOfBallots == 0;
	/**
	 * The total number of ballots in this ballot box.
	 */
    //@ public invariant numberOfBallots <= ballots.length;
	private /*@ spec_public @*/ int numberOfBallots;
	private int index;
	
	/**
	 * Create an empty ballot box.
	 */
	public /*@ pure @*/ BallotBox(){
		numberOfBallots = 0;
		ballots = new Ballot[Ballot.MAX_BALLOTS];
	} //@ nowarn;
	
	/**
	 * Accept a ballot paper.
	 * @param ballot The ballot paper
	 */
	/*@ requires numberOfBallots < ballots.length;
	  @ ensures \old(numberOfBallots) + 1 == numberOfBallots;
	  @ ensures (\exists int b; 0 <= b && b < numberOfBallots;
	  @         ballot.equals(ballots[b]));
	  @*/
	public void accept (/*@ non_null @*/ Ballot ballot) {
		ballots[numberOfBallots++] = ballot; //@ nowarn;
	} //@ nowarn;

	public boolean isNextBallot() {
		return index < numberOfBallots;
	}

	//@ requires 0 <= index;
	//@ requires index < ballots.length;
	public Ballot getNextBallot() {
		return ballots[index++];
	}
}