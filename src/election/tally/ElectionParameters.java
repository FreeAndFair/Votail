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
 * @author Dermot Cochran
 */

public class ElectionParameters {

/** Number of candidates for election in this constituency */
//@ public invariant 0 < numberOfCandidates;
	public int numberOfCandidates;
	
/** Number of seats to be filled in this election */
//@ public invariant 0 < numberOfSeatsInThisElection;
//@ public invariant numberOfSeatsInThisElection <= totalNumberOfSeats;
	public int numberOfSeatsInThisElection;
	
/** Number of seats in this constituency */
//@ public invariant 0 < totalNumberOfSeats;
	public int totalNumberOfSeats;
	
/** List of ID values for all candidates in this election */
/*@ public invariant (\forall int i;
  @   0 <= i && i < numberOfCandidates;
  @   0 < candidateIDs[i] &&
  @   candidateIDs[i] != Ballot.NONTRANSFERABLE); 
  @*/
// @constraint No duplicate candidate IDs are allowed. 	
/*@ public invariant (\forall int i, j;
  @   0 <= i && i < numberOfCandidates &&
  @   0 <= j && j < numberOfCandidates &&
  @   i != j;
  @   candidateIDs[i] != candidateIDs[j]); 
  @*/	
	public /*@ non_null @*/ long[] candidateIDs;

	private /*@ spec_public @*/ Candidate[] candidateList;
	
	public ElectionParameters(){	
		totalNumberOfSeats = 1;
		numberOfCandidates = 1;
		numberOfSeatsInThisElection = 1;
		candidateIDs = new long[numberOfCandidates];
	}

	public void setCandidateList(final Candidate[] candidateList) {
		this.candidateList = candidateList;
	}

	/*@ requires 0 < numberOfSeats;
	  @ ensures this.totalNumberOfSeats == numberOfSeats;
	  @*/
	/**
	 * @param numberOfSeats The total number of seats for election
	 */
	public void setNumberOfSeats(int numberOfSeats) {
		this.totalNumberOfSeats = numberOfSeats;
	}
};
