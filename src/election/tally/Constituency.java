package election.tally;

/*
 * Votail, (c) Dermot Cochran, 2005-2011
 * 
 * @author Dermot Cochran, 2005-2009, University College Dublin
 * 
 * @author Dermot Cochran, 2010-2011, IT Univeristy of Copenhagen
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
 *         Dermot Cochran</a>
 */
public class Constituency {
  private static final int MIN_CANDIDATES = 2;
  private static final int MIN_SEATS = 1;
  private static final int MIN_CONSTITUENCY_SIZE = 3;
  
  public Constituency(int numberOfCandidates, int numberOfSeatsInThisElection,
      int totalNumberOfSeats) {
    this.numberOfCandidates = numberOfCandidates;
    this.numberOfSeatsInThisElection = numberOfSeatsInThisElection;
    this.totalNumberOfSeats = totalNumberOfSeats;
  }
  
  public Constituency() {
    this.numberOfCandidates = Constituency.MIN_CANDIDATES;
    this.totalNumberOfSeats = MIN_CONSTITUENCY_SIZE;
    this.numberOfSeatsInThisElection = MIN_SEATS;
  }
  /** Number of candidates for election in this constituency */
  //@ public invariant numberOfSeatsInThisElection < numberOfCandidates;
  //@ public invariant numberOfCandidates <= Candidate.MAX_CANDIDATES;
  protected/*@ spec_public @*/int numberOfCandidates = 0;
  
  /** Number of seats to be filled in this election */
  //@ public invariant 0 <= numberOfSeatsInThisElection;
  protected/*@ spec_public @*/int numberOfSeatsInThisElection = 0;
  
  /** Number of seats in this constituency */
  //@ public invariant numberOfSeatsInThisElection <= totalNumberOfSeats;
  protected/*@ spec_public @*/int totalNumberOfSeats = 0;
  
  /** List of all candidates in this election */
  protected/*@ spec_public @*/Candidate[] candidateList;
  
  //@ public ghost boolean candidateDataInUse = false;
  
  /**
   * Get the <code>Candidate</code> object.
   * 
   * @return The candidate at that position on the initial list
   */
  //@ requires \nonnullelements (candidateList);
  //@ requires 0 <= index && index < candidateList.length;
  //@ ensures candidateList[index] == \result;
  public/*@ pure non_null @*/Candidate getCandidate(final int index) {
    return candidateList[index];
  }
  
  /**
   * Determine the number of candidates in this election.
   * 
   * @param number
   *          The number of candidates in this election.
   *          There must be at least two candidates or choices in any election.
   */
  //@ requires 2 <= number && number <= Candidate.MAX_CANDIDATES;
  //@ requires candidateDataInUse == false;
  //@ ensures number == this.numberOfCandidates;
  //@ ensures this.numberOfCandidates <= candidateList.length;
  public void setNumberOfCandidates(final int number) {
    this.numberOfCandidates = number;
    makeListOfCandidates();
    //@ set candidateDataInUse = true;
  }
  
  /**
   * Create the list of candidates.
   */
  //@ requires candidateDataInUse == false;
  //@ ensures this.numberOfCandidates <= this.candidateList.length;
  protected void makeListOfCandidates() {
    if (candidateList == null || candidateList.length < this.numberOfCandidates) {
      this.candidateList = new Candidate[this.numberOfCandidates];
      for (int index = 0; index < this.numberOfCandidates; index++) {
        this.candidateList[index] = new Candidate();
      }
    }
  }
  
  /**
   * Get the number of seats in this election
   * 
   * @return The number of seats for election
   */
  //@ ensures \result == numberOfSeatsInThisElection;
  public/*@ pure @*/int getNumberOfSeatsInThisElection() {
    return numberOfSeatsInThisElection;
  }
  
  /**
   * Get the total number of seats for a full general election
   * 
   * @return The total number of seats
   */
  //@ ensures \result == totalNumberOfSeats;
  public/*@ pure @*/int getTotalNumberOfSeats() {
    return totalNumberOfSeats;
  }
  
  //@ requires theNumberOfSeatsInElection <= theTotalNumberOfSeats;
  //@ requires 0 <= theNumberOfSeatsInElection;
  //@ assignable this.numberOfSeatsInThisElection;
  //@ assignable this.totalNumberOfSeats;
  //@ ensures this.numberOfSeatsInThisElection == theNumberOfSeatsInElection;
  //@ ensures this.totalNumberOfSeats == theTotalNumberOfSeats;
  public void setNumberOfSeats(final int theNumberOfSeatsInElection,
      final int theTotalNumberOfSeats) {
    this.totalNumberOfSeats = theTotalNumberOfSeats;
    this.numberOfSeatsInThisElection = theNumberOfSeatsInElection;
  }
  
  /**
   * Get the number of candidates running for election in this constituency.
   * 
   * @return The number of candidates.
   */
  //@ ensures \result == this.numberOfCandidates;
  public/*@ pure @*/int getNumberOfCandidates() {
    return this.numberOfCandidates;
  }
  
  /**
   * Load the list of candidates for this constituency.
   * 
   * @param candidateIDs
   *          The list of candidates
   * @param theNumberOfCandidates
   *          The number of candidates
   */
  //@ requires candidateDataInUse == false;
  //@ requires numberOfSeatsInThisElection < candidateIDs.length;
  //@ ensures \nonnullelements (candidateList);
  public void load(/*@ non_null @*/int[] candidateIDs) {
    this.numberOfCandidates = candidateIDs.length;
    //@ assert 0 <= this.numberOfCandidates;
    this.candidateList = new Candidate[candidateIDs.length];
    for (int index = 0; index < this.candidateList.length; index++) {
      this.candidateList[index] = new Candidate(candidateIDs[index]);
    }
    //@ set candidateDataInUse = true;
  }
}