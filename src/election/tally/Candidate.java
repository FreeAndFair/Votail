package election.tally;

import java.io.Serializable;

/**
 * The Candidate object records the number of votes received during each round
 * of counting. Votes can only be added to the candidate's stack while the
 * candidate has a status of <code>CONTINUING</code>.
 * 
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf"> Department of
 *      Environment and Local Government, Count Requirements and Commentary on
 *      Count Rules, section 3-14</a>
 * @author Dermot Cochran
 */

public class Candidate extends CandidateStatus implements Serializable {
  
  private static final long serialVersionUID = 3435036225909047966L;

  /**
   * Maximum expected number of candidates in any one constituency.
   * 
   * @see <a
   *      href="http://en.wikipedia.org/wiki/List_of_political_parties_in_the_Republic_of_Ireland">List
   *      of political parties in Ireland</a> The average number of candidates
   *      could be much less.
   */
  public static final int MAX_CANDIDATES = 50;
  
  /**
   * Identifier for the candidate. The data should be loaded in such a way that
   * the assignment of candidate IDs is fair and unbiased.
   */
  /*@ public invariant 0 <= candidateID;
    @ public constraint \old(candidateID) != NO_CANDIDATE
    @   ==> candidateID == \old(candidateID);
    @*/
  protected transient/*@ spec_public @*/int candidateID;
  
  /** Number of votes added at each count */
  /*@ public invariant (\forall int i; 0 < i && i < votesAdded.length;
    @   0 <= votesAdded[i]);
    @ public initially (\forall int i; 0 < i && i < votesAdded.length;
    @   votesAdded[i] == 0);
    @ public invariant votesAdded.length <= CountConfiguration.MAXCOUNT;
    @*/
  protected/*@ spec_public non_null @*/int[] votesAdded =
      new int[CountConfiguration.MAXCOUNT];
  
  /** Number of votes removed at each count */
  /*@ public invariant (\forall int i; 0 <= i && i < votesRemoved.length;
    @                                  0 <= votesRemoved[i]);
    @ public initially (\forall int i; 0 <= i && i < votesRemoved.length;
    @                                  votesRemoved[i] == 0);
    @ public invariant votesRemoved.length <= CountConfiguration.MAXCOUNT;
    @*/
  protected/*@ spec_public non_null @*/int[] votesRemoved =
      new int[CountConfiguration.MAXCOUNT];
  
  //@ public invariant votesAdded != votesRemoved;
  //@ public invariant votesRemoved != votesAdded;
  
  /** The number of rounds of counting so far */
  //@ public invariant 0 <= lastCountNumber;
  //@ public initially lastCountNumber == 0;
  //@ public constraint \old(lastCountNumber) <= lastCountNumber;
  //@ public invariant lastCountNumber < CountConfiguration.MAXCOUNT;
  //@ public invariant lastCountNumber < votesAdded.length;
  //@ public invariant lastCountNumber < votesRemoved.length;
  protected /*@ spec_public @*/ int lastCountNumber = 0;

  
  //@ protected initially totalVote == 0;
  //@ protected constraint \old(totalVote) <= totalVote;
  protected /*@ spec_public @*/ int totalVote = 0;

  
  /** Number of ballots transferred to another candidate*/
  /*@ protected initially removedVote == 0;
    @ protected invariant removedVote <= totalVote;
    @ protected constraint \old(removedVote) <= removedVote;
    @ protected invariant (state == CONTINUING) ==> removedVote == 0;
    @*/
  protected /*@ spec_public*/ int removedVote = 0;
    
  public static final int NO_CANDIDATE = 0;
  
  /**
   * Next available value for candidate ID number.
   */
  //@ private constraint \old(nextCandidateID) <= nextCandidateID;
  private /*@ spec_public @*/ static int nextCandidateID = MAX_CANDIDATES + 1;
  
  /**
   * Gets number of votes added or removed in this round of counting.
   * 
   * @param count
   *          This count number
   * @return A positive number if the candidate received transfers or a negative
   *         number if the candidate's surplus was distributed or the candidate
   *         was eliminated and votes transfered to another.
   */
  /*@ protected normal_behavior
    @   requires 0 <= count;
    @   requires count < votesAdded.length;
    @   requires count < votesRemoved.length;
    @   ensures \result == votesAdded[count] - votesRemoved[count];
    @*/
  protected/*@ pure spec_public @*/int getVoteAtCount(final int count) {
    return (votesAdded[count] - votesRemoved[count]);
  }
  
  /**
   * Total number of votes received by or added to this candidate.
   * 
   * @return Gross total of votes received
   */
  //@ ensures \result == totalVote;
  public/*@ pure @*/int getTotalVote() {
    
    return totalVote;
  }
  
  /**
   * Get status at the current round of counting; {@link #ELECTED},
   * {@link #ELIMINATED} or {@link #CONTINUING}
   * 
   * @return State value for this candidate
   */
  /*@ public normal_behavior
    @   ensures \result == state;
    @*/
  public/*@ pure @*/byte getStatus() {
    return state;
  }
  
  /**
   * Get the unique ID of this candidate.
   * 
   * @return The candidate ID number
   */
  /*@ public normal_behavior
    @   ensures \result == candidateID;
    @*/
  public/*@ pure @*/int getCandidateID() {
    return candidateID;
  }
  
  /**
   * This is the default constructor method for a <code>Candidate</code>
   */
  /*@ assignable candidateID, votesAdded, votesRemoved, nextCandidateID;
    @ ensures candidateID != nextCandidateID;
    @ ensures nextCandidateID != \old(nextCandidateID);
    @ ensures (\forall int i; 0 <= i && i < CountConfiguration.MAXCOUNT;
    @   getVoteAtCount() == 0);
    @*/
  public Candidate() {
    super();
    candidateID = nextCandidateID++;
    //@ loop_invariant (0 < i) ==> getVoteAtCount(i-1) == 0;
    for (int i = 0; i < CountConfiguration.MAXCOUNT; i++) {
      votesAdded[i] = 0;
      votesRemoved[i] = 0;
    }    
  }
  
  /**
   * Create a <code>candidate</code> where the identifier is already known
   * 
   * @param theCandidateID
   */
  /*@ requires 0 < theCandidateID;
    @ assignable candidateID, votesAdded, votesRemoved;
    @ ensures this.candidateID == theCandidateID;
    @ ensures (\forall int i; 0 <= i && i < CountConfiguration.MAXCOUNT;
    @   getTotalAtCount() == 0);
    @*/
  public Candidate(final int theCandidateID) {
    super();
    this.candidateID = theCandidateID;
    
    //@ loop_invariant (0 < i) ==> getVoteAtCount(i-1) == 0;
    for (int i = 0; i < CountConfiguration.MAXCOUNT; i++) {
      this.votesAdded[i] = 0;
      this.votesRemoved[i] = 0;
    }
  }
  
  /**
   * Add a number of votes to the candidate's ballot pile.
   * 
   * @design This method cannot be called twice for the same candidate in the
   *         same round of counting.
   * @param numberOfVotes
   *          Number of votes to add
   * @param count
   *          The round of counting at which the votes were added
   */
  /*@ public normal_behavior
    @   requires state == CONTINUING;
    @   requires lastCountNumber <= count;
    @   requires 0 <= count;
    @   requires count < votesAdded.length;
    @   requires 0 <= numberOfVotes;
    @   assignable lastCountNumber, votesAdded[count], totalVote;
    @   ensures \old(votesAdded[count]) + numberOfVotes == votesAdded[count];
    @   ensures \old(totalVote) + numberOfVotes == totalVote;
    @   ensures count == lastCountNumber;
    @*/
  public void addVote(final int numberOfVotes, final int count) {
    votesAdded[count] += numberOfVotes;
    totalVote += numberOfVotes;
    updateCountNumber(count);
  }
  
  /**
   * Update the last count number for this Candidate
   * 
   * @param count
   *          The number of the most recent count
   */
  /*@ protected normal_behavior
    @   requires count < CountConfiguration.MAXCOUNT;
    @   requires count < votesAdded.length;
    @   requires count < votesRemoved.length;
    @   requires lastCountNumber <= count;
    @   assignable lastCountNumber;
    @   ensures lastCountNumber == count;
    @*/
  protected void updateCountNumber(final int count) {
    lastCountNumber = count;
  }
  
  /**
   * Removes a number of votes from a candidates ballot stack.
   * 
   * @design This method cannot be called twice for the same candidate in the
   *         same round of counting.
   * @param numberOfVotes
   *          Number of votes to remove from this candidate
   * @param count
   *          The round of counting at which the votes were removed
   */
  /*@ public normal_behavior
    @   requires state == ELIMINATED || state == ELECTED;
    @   requires lastCountNumber <= count;
    @   requires 0 <= count;
    @   requires count < votesRemoved.length;
    @   requires count < votesAdded.length;
    @   requires count < CountConfiguration.MAXCOUNT;
    @   requires 0 <= numberOfVotes;
    @   requires numberOfVotes <= getTotalAtCount();
    @   assignable lastCountNumber, votesRemoved[count], removedVote;
    @   ensures \old(votesRemoved[count]) + numberOfVotes == votesRemoved[count];
    @   ensures \old(removedVote) + numberOfVotes == removedVote;
    @   ensures count == lastCountNumber;
    @*/
  public void removeVote(final int numberOfVotes, final int count) {
    votesRemoved[count] += numberOfVotes;
    removedVote += numberOfVotes;
    updateCountNumber(count);
  }
  
  /** Declares the candidate to be elected */
  /*@ public normal_behavior
    @   requires this.state == CONTINUING;
    @   requires this.lastCountNumber <= countNumber;
    @   requires 0 <= countNumber && countNumber < CountConfiguration.MAXCOUNT;
    @   requires countNumber < votesAdded.length;
    @   requires countNumber < votesRemoved.length;
    @   assignable state, lastCountNumber;
    @   ensures state == ELECTED;
    @*/
  public void declareElected(final int countNumber) {
    updateCountNumber(countNumber);
    state = ELECTED;
  }
  
  /** Declares the candidate to be eliminated */
  /*@ public normal_behavior
    @   requires 0 <= countNumber && countNumber < CountConfiguration.MAXCOUNT;
    @   requires countNumber < votesAdded.length;
    @   requires countNumber < votesRemoved.length;
    @   requires this.lastCountNumber <= countNumber;
    @   requires this.state == CONTINUING;
    @   assignable state, lastCountNumber;
    @   ensures state == ELIMINATED;
    @*/
  public void declareEliminated(final int countNumber) {
    updateCountNumber(countNumber);
    state = ELIMINATED;
  }
  
  /**
   * Determines the relative ordering of the candidate in the event of a tie.
   * 
   * @param other
   *          The other candidate to compare with this candidate
   * @return <code>true</true> if other candidate is not selected
   */
  /*@ 
    @ public normal_behavior
    @   ensures (\result == true) <==> (this.candidateID > other.candidateID);
    @*/
  public/*@ pure @*/boolean isAfter(final/*@ non_null @*/Candidate other) {
    return (this.candidateID > other.candidateID);
  }
  
  /**
   * Is this the same candidate?
   * 
   * @param other
   *          The candidate to be compared
   * @return <code>true</code> if this is the same candidate
   */
  /*@ public normal_behavior
    @   ensures \result <==> ((other != null) &&
    @     (other.candidateID == candidateID));
    @*/
  public/*@ pure @*/boolean sameAs(/*@ non_null @*/final Candidate other) {
    return (other.candidateID == this.candidateID);
  }
  
  /**
   * How many votes have been received by this round of counting?
   * 
   * @return The total number of votes received so far
   */
  //@ ensures \result == totalVote - removedVote;
  public/*@ pure @*/int getTotalAtCount() {
    
    return totalVote - removedVote;
  }
  
  /**
   * Has this candidate been elected?
   * 
   * @return <code>true</code> if elected
   */
  //@ ensures (\result == true) <==> (state == ELECTED);
  public/*@ pure*/boolean isElected() {
    return state == ELECTED;
  }
  
  /**
   * Summary of candidate information, excluding transfers
   */
  public/*@ non_null pure*/String toString() {
    final StringBuffer stringBuffer = new StringBuffer(60);
    stringBuffer.append("Candidate");
    stringBuffer.append(Integer.toString(candidateID));
    if (isElected()) {
      stringBuffer.append(" elected");
    }
    else {
      stringBuffer.append(" lost");
    }
    stringBuffer.append(" with ");
    stringBuffer.append(Integer.toString(getTotalVote()));
    stringBuffer.append(" votes");

    return stringBuffer.toString();
  }
  
  //@ ensures \result <==> (state == ELIMINATED);
  public/*@ pure*/boolean isEliminated() {
    return state == ELIMINATED;
  }
}