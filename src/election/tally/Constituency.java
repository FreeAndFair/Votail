package election.tally;

import java.io.Serializable;

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
public class Constituency implements Serializable {
  
  /**
   * 
   */
  private static final long serialVersionUID = -6070877545836273536L;

  public Constituency() {
    this.candidates = Candidate.MAX_CANDIDATES;
    this.totalSeatsInConstituency = 1;
    this.seatsInThisElection = 1;
  }
  /** Number of candidates for election in this constituency */
  //@ public invariant 0 < candidates;
  //@ public invariant seatsInThisElection < candidates;
  //@ public invariant candidates <= Candidate.MAX_CANDIDATES;
  protected/*@ spec_public @*/int candidates;
  
  /** Number of seats to be filled in this election */
  //@ public invariant 0 < seatsInThisElection;
  protected/*@ spec_public @*/int seatsInThisElection;
  
  /** Number of seats in this constituency */
  //@ public invariant seatsInThisElection <= totalSeatsInConstituency;
  protected/*@ spec_public @*/int totalSeatsInConstituency;
  
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
   *        The number of candidates in this election.
   *        There must be at least two candidates or choices in any election.
   */
  //@ requires 2 <= number && number <= Candidate.MAX_CANDIDATES;
  //@ requires seatsInThisElection < number;
  //@ requires candidateDataInUse == false;
  //@ ensures number == this.candidates;
  //@ ensures this.candidates <= candidateList.length;
  //@ ensures candidateDataInUse == true;
  public void setNumberOfCandidates(final int number) {
    this.candidates = number;
    if (candidateList == null || candidateList.length < this.candidates) {
      this.candidateList = new Candidate[this.candidates];
      
      //@ loop_invariant (0 < index) ==> candidateList[index-1] != null;
      for (int index = 0; index < this.candidates; index++) {
        this.candidateList[index] = new Candidate();
      }
    }
    //@ set candidateDataInUse = true;
  }
  
  /**
   * Get the number of seats in this election
   * 
   * @return The number of seats for election
   */
  //@ ensures \result == seatsInThisElection;
  public/*@ pure @*/int getNumberOfSeatsInThisElection() {
    return seatsInThisElection;
  }
  
  /**
   * Get the total number of seats for a full general election
   * 
   * @return The total number of seats
   */
  //@ ensures \result == totalSeatsInConstituency;
  public/*@ pure @*/int getTotalNumberOfSeats() {
    return totalSeatsInConstituency;
  }
  
  //@ requires seatsInElection <= seatsInConstituency;
  //@ requires 0 < seatsInElection;
  //@ requires seatsInElection < candidates;
  //@ assignable seatsInThisElection;
  //@ assignable totalSeatsInConstituency;
  //@ ensures seatsInThisElection == seatsInElection;
  //@ ensures totalSeatsInConstituency == seatsInConstituency;
  public void setNumberOfSeats(final int seatsInElection,
      final int seatsInConstituency) {
    totalSeatsInConstituency = seatsInConstituency;
    seatsInThisElection = seatsInElection;
  }
  
  /**
   * Get the number of candidates running for election in this constituency.
   * 
   * @return The number of candidates.
   */
  //@ ensures \result == this.candidates;
  public/*@ pure @*/int getNumberOfCandidates() {
    return this.candidates;
  }
  
  /**
   * Load the list of candidates for this constituency.
   * 
   * @param candidateIDs
   *        The list of candidate identifiers corresponding to the encoding
   *        of the ballots
   */
  //@ requires candidateDataInUse == false;
  //@ requires seatsInThisElection < candidateIDs.length;
  /*@ requires (\forall int i; 0 <= i && i < candidateIDs.length;
    @   0 < candidateIDs[i]);
    @*/
  //@ assignable candidates, candidateList, candidateDataInUse, candidateList[*];
  //@ ensures \nonnullelements (candidateList);
  //@ ensures candidateDataInUse == true;
  //@ ensures candidateList.length == candidateIDs.length;
  //@ ensures candidates == candidateIDs.length;
  public void load(final /*@ non_null @*/int[] candidateIDs) {
    this.candidates = candidateIDs.length;
    this.candidateList = new Candidate[candidateIDs.length];
    /*@ loop_invariant (0 < index) ==>
      @   candidateList[index-1].getCandidateID() ==
      @   candidateIDs[index-1];
      @*/
    for (int index = 0; index < this.candidateList.length; index++) {
      final int theCandidateID = candidateIDs[index];
      this.candidateList[index] = new Candidate(theCandidateID);
    }
    //@ set candidateDataInUse = true;
  }
}