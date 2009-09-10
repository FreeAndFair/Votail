package election.tally;

/*
 * Copyright (c) 2005-2009 Dermot Cochran
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
 * Data transfer structure for candidate ID details and number of seats.
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */

public class Election {

/** Number of candidates for election in this constituency */
//@ public invariant 0 <= numberOfCandidates;
//@ public invariant numberOfCandidates <= Candidate.MAX_CANDIDATES;
	protected /*@ spec_public @*/ transient int numberOfCandidates;
	
/** Number of seats to be filled in this election */
//@ public invariant 0 <= numberOfSeatsInThisElection;
//@ public invariant numberOfSeatsInThisElection <= totalNumberOfSeats;
	public transient int numberOfSeatsInThisElection;
	
/** Number of seats in this constituency */
//@ public invariant 0 <= totalNumberOfSeats;
	public transient int totalNumberOfSeats;
	
/** List of all candidates in this election */
/*@ public invariant (\forall int i;
  @   0 <= i && i < numberOfCandidates;
  @   0 < candidateList[i].getCandidateID() &&
  @   candidateList[i].getCandidateID() != Ballot.NONTRANSFERABLE); 
  @*/
/** @constraint No duplicate candidates are allowed. */
/*@ public invariant (\forall int i, j;
  @   0 <= i && i < numberOfCandidates &&
  @   0 <= j && j < numberOfCandidates &&
  @   i != j;
  @   candidateList[i].candidateID != candidateList[j].candidateID); 
  @*/	
  protected /*@ spec_public non_null @*/ Candidate[] candidateList;

    /**
     * Election parameters e.g. number of seats
     */
	public Election(){	
		totalNumberOfSeats = 0;
		numberOfCandidates = 0;
		numberOfSeatsInThisElection = totalNumberOfSeats;
		candidateList = new Candidate [Candidate.MAX_CANDIDATES];
		for (int i = 0; i < Candidate.MAX_CANDIDATES; i++) {
      candidateList[i] = new Candidate();
      }
		//@ assert candidateList.length == Candidate.MAX_CANDIDATES;
    }

	/**
	 * Get the <code>Candidate</code> object.
	 * 
	 * @return The candidate at that position on the initial list
	 */
	//@ requires candidateList != null && candidateList[index] != null;
	//@ requires 0 <= index && index < candidateList.length;
	public /*@ pure non_null @*/ Candidate getCandidate(final int index) {
		return candidateList[index];
	}

  /**
   * Determine the number of candidates in this election.
   * 
   * @param n The number of candidates in this election
   */
  //@ requires 1 <= n;
	//@ requires n <= Candidate.MAX_CANDIDATES;
  //@ ensures n == numberOfCandidates;
  public void setNumberOfCandidates(int n) {
    
    numberOfCandidates = n;
  }
}
