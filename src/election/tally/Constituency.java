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
 * Size of constituency and list of candidates for election..
 * 
 * @author <a href="http://kind.ucd.ie/documents/research/lgsse/evoting.html">
 * Dermot Cochran</a>
 */

public class Constituency {

  /** Number of candidates for election in this constituency */
  //@ public invariant 0 <= numberOfCandidates;
  //@ public invariant numberOfCandidates <= Candidate.MAX_CANDIDATES;
	protected /*@ spec_public @*/ transient int numberOfCandidates = 0;
	
  /** Number of seats to be filled in this election */
  //@ public invariant 0 <= numberOfSeatsInThisElection;
  //@ public invariant numberOfSeatsInThisElection <= totalNumberOfSeats;
	protected /*@ spec_public @*/ transient int numberOfSeatsInThisElection = 0;
	
  /** Number of seats in this constituency */
  //@ public invariant 0 <= totalNumberOfSeats;
	protected /*@ spec_public @*/ transient int totalNumberOfSeats = 0;
	
  /** List of all candidates in this election */
  //@ public invariant \nonnullelements (candidateList);
  protected /*@ spec_public non_null @*/ Candidate[] candidateList = new Candidate[0];

  //@ public ghost boolean candidateDataInUse = false;
  
	/**
	 * Get the <code>Candidate</code> object.
	 * 
	 * @return The candidate at that position on the initial list
	 */
	//@ requires \nonnullelements (candidateList);
	//@ requires 0 <= index && index < numberOfCandidates;
	//@ ensures candidateList[index] == \result;
	public /*@ pure non_null @*/ Candidate getCandidate(final int index) {
    return candidateList[index];
	}

  /**
   * Determine the number of candidates in this election.
   * 
   * @param number The number of candidates in this election. 
   *   There must be at least two candidates or choices in any election.
   */
  //@ requires 2 <= number;
	//@ requires number <= Candidate.MAX_CANDIDATES;
	//@ requires candidateDataInUse == false;
  //@ ensures number == numberOfCandidates;
	//@ ensures number <= candidateList.length;
  public void setNumberOfCandidates(final int number) {
      this.numberOfCandidates = number;
      makeListOfCandidates();
      //@ set candidateDataInUse = true;
  }
  
  private void makeListOfCandidates() {
    if (this.candidateList.length < this.numberOfCandidates) {
      this.candidateList = new Candidate[this.numberOfCandidates];
      for (int index=0; index < this.numberOfCandidates; index++) {
        this.candidateList[index] = new Candidate();
      }
    }
  }

  public /*@ pure @*/ int getNumberOfSeatsInThisElection() {
    return numberOfSeatsInThisElection;
  }

  public /*@ pure @*/ int getTotalNumberOfSeats() {
    return totalNumberOfSeats;
  }

  //@ requires numberOfSeatsInThisElection <= totalNumberOfSeats;
  //@ requires 0 <= numberOfSeatsInThisElection;
  public void setNumberOfSeats(
     final int numberOfSeatsInThisElection, final int totalNumberOfSeats) {
    this.numberOfSeatsInThisElection = numberOfSeatsInThisElection;
    this.totalNumberOfSeats = totalNumberOfSeats;
  }

  //@ ensures \result == numberOfCandidates;
  public /*@ pure @*/ int getNumberOfCandidates() {
    return numberOfCandidates;
  }
}
