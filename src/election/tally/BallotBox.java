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

/** Data transfer structure for set of all valid ballots */
public class BallotBox {
	
/**
 * List of valid ballot papers, already shuffled and mixed by the data loader
 * or returning officer.
 */
  //@ public invariant \nonnullelements (ballots);
  // TODO JML warning: array nullity is invariant for assignment
  protected /*@ non_null spec_public @*/ Ballot[] ballots = new Ballot [Ballot.MAX_BALLOTS];

    /**
     * Get the number of ballots in this box.
     * 
     * @return the number of ballots in this ballot box
     */	
   /*@ public normal_behavior
     @   ensures 0 <= \result;
     @   ensures \result == numberOfBallots;
     @   ensures (ballots == null) ==> \result == 0;
     @*/
    public /*@ pure @*/ int size(){
        return numberOfBallots;
    }
	
  /**
   * The total number of ballots in this ballot box.
   */
    /*@ public invariant 0 <= numberOfBallots;
      @ public invariant numberOfBallots <= Ballot.MAX_BALLOTS;
      @ public constraint \old (numberOfBallots) <= numberOfBallots;
      @*/
	protected /*@ spec_public @*/ int numberOfBallots;
	
	/**
	 * Number of ballots copied from box
	 */
	//@ public initially index == 0;
	//@ public invariant index <= size();
	//@ public constraint \old(index) <= index;
 	protected /*@ spec_public @*/ int index;
	
	/**
	 * Create an empty ballot box.
	 */
 	//@ assignable ballots, index, numberOfBallots;
	public /*@ pure @*/ BallotBox(){
		index = 0;
		numberOfBallots = 0;
		final int[] preferences = new int[0];
		for (int b=0; b < ballots.length; b++) {
		  // TODO 2009.10.15 ESC assignable warning
		  ballots[b] = new Ballot(preferences); //@ nowarn;
		}
	}

	/**
	 * Accept an anonymous ballot paper.
	 * <p>
	 * The ballot ID number is regenerated.
	 * <p>
	 * @param ballot The ballot paper
	 */
	/*@ requires numberOfBallots < ballots.length;
	  @ requires numberOfBallots < Ballot.MAX_BALLOTS;
	  @ requires ballots[numberOfBallots].positionInList == 0;
	  @ ensures \old(numberOfBallots) + 1 == numberOfBallots;
	  @*/
	public void accept (final /*@ non_null @*/ int[] preferences) {
	  //@ assert ballots[numberOfBallots] != null;
	  // TODO 2009.10.15 ESC type mismatch warning
		ballots[numberOfBallots++] = new Ballot(preferences); //@ nowarn;
	} 

	/**
	 * Is there another ballot paper?
	 * @return <code>true</code>if there is
	 */
	//@ ensures \result <==> index < numberOfBallots;
	public /*@ pure @*/ boolean isNextBallot() {
		return index < numberOfBallots;
	}

	/**
	 * Get the next ballot paper
	 * @return The ballot paper
	 */
	//@ requires 0 <= index;
	//@ requires isNextBallot();
	//@ requires index + 1 < ballots.length;
	//@ assignable index;
	//@ ensures \result == ballots[\old(index)];
    public Ballot getNextBallot() {
      return ballots[index++];
    }
}