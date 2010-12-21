package election.tally;

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

public class Candidate extends CandidateStatus {

  /**
   * Maximum expected number of candidates in any one constituency.
   * 
   * @see <a
   *      href="http://en.wikipedia.org/wiki/List_of_political_parties_in_the_Republic_of_Ireland">List
   *      of political parties in Ireland</a> The average number of candidates
   *      could be much less.
   */
  public static final int MAX_CANDIDATES = 20;

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
    @ public invariant votesAdded.length == CountConfiguration.MAXCOUNT;
    @*/
  protected/*@ spec_public non_null @*/int[] votesAdded =
                                                           new int[CountConfiguration.MAXCOUNT];

  /** Number of votes removed at each count */
  /*@ public invariant (\forall int i; 0 < i && i < votesRemoved.length;
    @                                  0 <= votesRemoved[i]);
    @ public initially (\forall int i; 0 < i && i < votesRemoved.length;
    @                                  votesRemoved[i] == 0);
    @ public invariant votesRemoved.length == CountConfiguration.MAXCOUNT;
    @*/
  protected/*@ spec_public non_null @*/int[] votesRemoved =
                                                             new int[CountConfiguration.MAXCOUNT];

  //@ public invariant votesAdded != votesRemoved;
  //@ public invariant votesRemoved != votesAdded;

  /** The status of the candidate at the latest count */
  /*@ public invariant state == ELECTED || state == ELIMINATED ||
    @   state == CONTINUING;
    @ public initially state == CONTINUING;
    @*/
  protected transient/*@ spec_public @*/byte state;

  /** The number of rounds of counting so far */
  //@ public invariant 0 <= lastCountNumber;
  //@ public initially lastCountNumber == 0;
  //@ public constraint \old(lastCountNumber) <= lastCountNumber;
  //@ public invariant lastCountNumber <= CountConfiguration.MAXCOUNT;
  protected transient/*@ spec_public @*/int lastCountNumber;

  public static final int NO_CANDIDATE = 0;

  /**
   * Next available value for candidate ID number.
   */
  //@ private constraint \old(nextCandidateID) <= nextCandidateID;
  private static int nextCandidateID = MAX_CANDIDATES + 1;

  /**
   * Gets number of votes added or removed in this round of counting.
   * 
   * @param count
   *        This count number
   * @return A positive number if the candidate received transfers or a negative
   *         number if the candidate's surplus was distributed or the candidate
   *         was eliminated and votes transfered to another.
   */
  /*@ protected normal_behavior
    @   requires 0 <= count;
    @   requires count < CountConfiguration.MAXCOUNT;
    @   requires votesAdded.length == CountConfiguration.MAXCOUNT;
    @   requires votesRemoved.length == CountConfiguration.MAXCOUNT;
    @   ensures \result == votesAdded[count] - votesRemoved[count];
    @*/
  protected/*@ pure @*/int getVoteAtCount(final int count) {
    return (votesAdded[count] - votesRemoved[count]);
  }

  /**
   * Original number of votes received by this candidate before transfers due to
   * elimination or distribution of surplus votes.
   * 
   * @return Gross total of votes received
   */
  /*@ requires lastCountNumber < votesAdded.length;
    @
    @*/
  public/*@ pure @*/int getOriginalVote() {
    int originalVote = 0;

    for (int i = 0; i <= lastCountNumber; i++) {
      originalVote += votesAdded[i];
    }

    return originalVote;
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
  /*@ ensures state == CONTINUING;
    @ ensures lastCountNumber == 0;
    @*/
  public Candidate() {
    super();
    candidateID = getUniqueID();
    initialiseVotes();
  }

  /**
 * 
 */
  protected void initialiseVotes() {
    state = CONTINUING;
    for (int i = 0; i < CountConfiguration.MAXCOUNT; i++) {
      votesAdded[i] = 0;
      votesRemoved[i] = 0;
    }
    lastCountNumber = 0;
  }

  /**
   * Create a <code>candidate</code> where the identifier is already known
   * 
   * @param theCandidateID
   */
  public Candidate(int theCandidateID) {
    if (0 < theCandidateID) {
      this.candidateID = theCandidateID;
    }
    else {
      this.candidateID = getUniqueID();
    }
    initialiseVotes();
  }

  public static int getUniqueID() {
    return nextCandidateID++;
  }

  /**
   * Add a number of votes to the candidate's ballot pile.
   * 
   * @design This method cannot be called twice for the same candidate in the
   *         same round of counting.
   * @param numberOfVotes
   *        Number of votes to add
   * @param count
   *        The round of counting at which the votes were added
   */
  /*@ public normal_behavior
    @   requires state == CONTINUING;
    @   requires lastCountNumber <= count;
    @   requires 0 <= count;
    @   requires count < votesAdded.length;
    @   requires 0 <= numberOfVotes;
    @   assignable lastCountNumber, votesAdded[count];
    @   ensures numberOfVotes <= votesAdded[count];
    @   ensures lastCountNumber == count;
    @*/
  public void addVote(final int numberOfVotes, final int count) {
    votesAdded[count] += numberOfVotes;
    lastCountNumber = count;
  }

  /**
   * Removes a number of votes from a candidates ballot stack.
   * 
   * @design This method cannot be called twice for the same candidate in the
   *         same round of counting.
   * @param numberOfVotes
   *        Number of votes to remove from this candidate
   * @param count
   *        The round of counting at which the votes were removed
   */
  /*@ public normal_behavior
    @   requires state == ELIMINATED || state == ELECTED;
    @   requires lastCountNumber <= count;
    @   requires 0 <= count;
    @   requires count < votesRemoved.length;
    @   requires 0 <= numberOfVotes;
    @   requires numberOfVotes <= getTotalAtCount(count);
    @   assignable lastCountNumber, votesRemoved[count];
    @   ensures numberOfVotes <= votesRemoved[count];
    @   ensures lastCountNumber == count;
    @*/
  public void removeVote(final int numberOfVotes, final int count) {
    votesRemoved[count] += numberOfVotes;
    lastCountNumber = count;
  }

  /** Declares the candidate to be elected */
  /*@ public normal_behavior
    @   requires state == CONTINUING;
    @   assignable state;
    @   ensures state == ELECTED;
    @*/
  public void declareElected() {
    state = ELECTED;
  }

  /** Declares the candidate to be eliminated */
  /*@ public normal_behavior
    @   requires state == CONTINUING;
    @   assignable this.state;
    @   ensures state == ELIMINATED;
    @*/
  public void declareEliminated() {
    state = ELIMINATED;
  }

  /**
   * Determines the relative ordering of the candidate in the event of a tie.
   * 
   * @param other
   *        The other candidate to compare with this candidate
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
   *        The candidate to be compared
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
   * @param count
   *        The round of counting
   * @return The total number of votes received so far
   */
  /*@ requires 0 <= count;
    @ requires count < CountConfiguration.MAXCOUNT;
    @ requires votesAdded.length == CountConfiguration.MAXCOUNT;
    @ requires votesRemoved.length == CountConfiguration.MAXCOUNT;
    @*/
  public/*@ pure @*/int getTotalAtCount(final int count) {
    int totalAtCount = 0;

    for (int i = 0; i <= count; i++) {
      totalAtCount += getVoteAtCount(i);
    }

    return totalAtCount;
  }

  /**
   * Has this candidate been elected?
   * 
   * @return <code>true</code> if elected
   */
  public/*@ pure @*/boolean isElected() {
    return (getStatus() == ELECTED);
  }

  /**
   * Summary of candidate information, excluding transfers
   */
  public String toString() {
    StringBuffer stringBuffer = new StringBuffer("Candidate ID " + candidateID);
    if (isElected()) {
      stringBuffer.append(" elected");
    } else if (state == ELIMINATED) {
      stringBuffer.append(" excluded");
    } else {
      stringBuffer.append(" continuing");
    }
    stringBuffer.append(" on round " + lastCountNumber + " with "
                        + getOriginalVote() + " votes");
    return stringBuffer.toString();
  }
}