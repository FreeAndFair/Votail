package election.tally;

/** 
 * The Candidate object records the number of votes received during
 * each round of counting. Votes can only be added to the candidate's
 * stack while the candidate has a status of <code>CONTINUING</code>.
 * 
 * @see <a href="http://www.cev.ie/htm/tenders/pdf/1_2.pdf">
 * Department of Environment and Local Government, 
 * Count Requirements and Commentary on Count Rules,
 * section 3-14</a>
 * 
 * @author Dermot Cochran
 * @copyright 2005-2009
 */

public class Candidate extends CandidateStatus {
	
/**
 * Maximum expected number of candidates in any one constituency.
 * 
 * @see <a href="http://en.wikipedia.org/wiki/List_of_political_parties_in_the_Republic_of_Ireland">
 * List of political parties in Ireland</a>	
 * 
 * The average number of candidates could be much less.
 */
public static final int MAX_CANDIDATES = 50;

/** Identifier for the candidate.
 */
/*@ public invariant 0 <= candidateID;
  @ public constraint candidateID == \old(candidateID);
  @*/
	protected transient /*@ spec_public @*/ int candidateID;
	
/** Number of votes added at each count */
/*@ public invariant (\forall int i; 0 < i && i < votesAdded.length;
  @   0 <= votesAdded[i]);
  @ public initially (\forall int i; 0 < i && i < votesAdded.length;
  @   votesAdded[i] == 0);	
  @ public invariant votesAdded.length <= CountConfiguration.MAXCOUNT;
  @*/
  protected /*@ spec_public non_null @*/ int[] votesAdded 
    = new int [CountConfiguration.MAXCOUNT];
	
/** Number of votes removed at each count */
/*@ public invariant (\forall int i; 0 < i && i < votesRemoved.length;
  @                                  0 <= votesRemoved[i]);
  @ public initially (\forall int i; 0 < i && i < votesRemoved.length;
  @                                  votesRemoved[i] == 0);
  @ public invariant votesRemoved.length <= CountConfiguration.MAXCOUNT;
  @*/
  protected /*@ spec_public non_null @*/ int[] votesRemoved 
    = new int [CountConfiguration.MAXCOUNT];

//@ public invariant votesAdded != votesRemoved;
//@ public invariant votesRemoved != votesAdded;
	
/** The status of the candidate at the latest count */
/*@ public invariant state == ELECTED || state == ELIMINATED ||
  @   state == CONTINUING;
  @ public initially state == CONTINUING;
  @*/      
	protected transient /*@ spec_public @*/ byte state;

/** The number of rounds of counting so far */
//@ public invariant 0 <= lastCountNumber;
//@ public initially lastCountNumber == 0;
//@ public constraint \old(lastCountNumber) <= lastCountNumber;
//@ public invariant lastCountNumber <= CountConfiguration.MAXCOUNT;
	protected transient /*@ spec_public @*/ int lastCountNumber;

/** The count number at which the last set of votes were added */
//@ public invariant 0 <= lastSetCount;
//@ public initially lastSetCount == 0;	
//@ public constraint \old(lastSetCount) <= lastSetCount;
//@ public invariant lastSetCount <= lastCountNumber;
	protected transient /*@ spec_public @*/ int lastSetCount;

/**
 * Unique random number used to simulate drawing of lots between candidates.
 */
  protected transient /*@ spec_public @*/ int randomNumber;
  //@ ghost int _randomNumber;

  /**
 * Total number of votes this candidate has at any time 
 * 
 * @design This variable was added as to provide easy access from other classes.
 */
	public int total;

public static final int NO_CANDIDATE = 0;

	/**
	 * Next available value for candidate ID number. 
	 */
//@ private constraint \old(nextCandidateID) <= nextCandidateID;
private static int nextCandidateID = 1;

	
/**
 * Gets number of votes added or removed in this round of counting.
 * 
 * @param count This count number
 * @return A positive number if the candidate received transfers or 
 * a negative number if the candidate's surplus was distributed or 
 * the candidate was eliminated and votes transfered to another. 
 */	
/*@ 
  @   public normal_behavior
  @     requires votesAdded != null;
  @     requires votesRemoved != null;
  @     requires 0 <= count;
  @     requires count <= lastCountNumber;
  @     ensures \result == votesAdded[count] - votesRemoved[count];
  @*/
	public /*@ pure @*/ int getVoteAtCount(final int count){
		return (votesAdded[count] - votesRemoved[count]);
	}
	
/*@ ensures \result == (\sum int i; 0 <= i && i <= lastCountNumber;
  @     ((votesAdded[i]) - (votesRemoved[i])));
  @
  @ public pure model int sumOfRetainedVotes() {
  @     int sum = 0;
  @
  @     for (int i = 0; i <= lastCountNumber; i++) {
  @		   sum += votesAdded[i];
  @        sum -= votesRemoved[i];
  @		}
  @
  @     return sum;
  @ }
  @*/
	
	/*@ ensures \result == (\sum int i; 0 <= i && i <= lastCountNumber;
	  @     (votesAdded[i]));
	  @
	  @ public pure model int sumOfAllVotes() {
	  @     int sum = 0;
	  @
	  @     for (int i = 0; i <= lastCountNumber; i++) {
	  @		   sum += votesAdded[i];
	  @		}
	  @
	  @     return sum;
	  @ }
	  @*/
  	
/**
 * Original number of votes received by this candidate before
 * transfers due to elimination or distribution of surplus votes.
 * 
 * @return Gross total of votes received 
 */	
/*@ public normal_behavior
  @   ensures \result == sumOfAllVotes();
  @   ensures 0 <= \result;
  @*/
	public /*@ pure @*/ int getOriginalVote() {
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
 *  @return State value for this candidate
 */
/*@ public normal_behavior
  @   ensures \result == state;
  @*/	
	public /*@ pure @*/ byte getStatus(){
		return state;
	}
	
/**
 * Get the unique ID of this candidate.
 * 
 * @return The candidate ID number
 */
/*@ 
  @   public normal_behavior
  @   ensures \result == candidateID;
  @*/	
	public /*@ pure @*/ int getCandidateID() {
 		return candidateID;
	}
	
/**
 * This is the default constructor method for a <code>Candidate</code>
 */	
  public Candidate(){
    state = CONTINUING;
    randomNumber = this.hashCode();
    candidateID = nextCandidateID++;
    //@ set _randomNumber = randomNumber;
  }

/**
 * Add a number of votes to the candidate's ballot pile.
 * 
 * @design This method cannot be called twice for the same candidate
 * in the same round of counting.
 * 
 * @param numberOfVotes Number of votes to add
 * @param count The round of counting at which the votes were added
 */	
/*@  
  @   public normal_behavior
  @   requires state == CONTINUING;
  @   requires lastCountNumber < count || 
  @            (lastCountNumber == 0 && count == 0);
  @   requires votesAdded[count] == 0;
  @   requires 0 <= count && count <= votesAdded.length;
  @   requires 0 <= numberOfVotes;
  @   assignable lastCountNumber, votesAdded[count], lastSetCount;
  @   ensures votesAdded[count] == numberOfVotes;
  @   ensures lastCountNumber == count;
  @   ensures lastSetCount == count;
  @*/
  public void addVote(final int numberOfVotes, final int count){
       votesAdded[count] += numberOfVotes;
       lastCountNumber = count;
       lastSetCount = count;
  }

/**
 * Removes a number of votes from a candidates ballot stack.
 * 
 * @design This method cannot be called twice for the same candidate
 * in the same round of counting.
 * 
 * @param numberOfVotes Number of votes to remove from this candidate
 * @param count The round of counting at which the votes were removed 
 */	
/*@ public normal_behavior
  @   requires state == ELIMINATED || state == ELECTED;
  @   requires lastCountNumber <= count;
  @   requires votesRemoved != null && votesRemoved[count] == 0;
  @   requires 0 <= count;
  @   requires votesRemoved != null && count < votesRemoved.length;
  @   requires 0 <= numberOfVotes;
  @   requires numberOfVotes <= getTotalVote();
  @   assignable lastCountNumber, votesRemoved[count];
  @   ensures \old(getTotalVote()) == getTotalVote() + numberOfVotes;
  @   ensures lastCountNumber == count;
  @*/
  public void removeVote(final int numberOfVotes, final int count){
        votesRemoved[count] += numberOfVotes;
        lastCountNumber = count;
    }

/** Declares the candidate to be elected */
/*@ public normal_behavior
  @   requires state == CONTINUING;
  @   assignable state;
  @   ensures state == ELECTED;
  @*/
	public void declareElected(){
		state = ELECTED;
	} //@ nowarn;
	
/** Declares the candidate to be eliminated */
/*@ public normal_behavior
  @   requires state == CONTINUING;
  @   assignable state;
  @   ensures state == ELIMINATED;
  @*/
	public void declareEliminated(){
		state = ELIMINATED;
	} //@ nowarn;

/**
 * Compares with another candidate's secret random number.
 * 
 * @design It is intended to be able to compare random numbers without
 * revealing the exact value of the random number, so that the random
 * number cannot be manipulated in any way.
 * 
 * @param other other candidate to compare with this candidate
 * 
 * @return <code>true</true> if other candidate has lower random number
 */	
/*@ 
  @ public normal_behavior
  @ ensures (\result == true) <==>
  @   (this.randomNumber > other.randomNumber);
  @*/
	public /*@ pure @*/ boolean isAfter(final /*@ non_null @*/ Candidate other){
		return (this.randomNumber > other.randomNumber);
	}
	
/**
 * Is this the same candidate?
 * 
 * @param other The candidate to be compared
 * 
 * @return <code>true</code> if this is the same candidate
 */
/*@ public normal_behavior
  @   ensures \result <==> ((other != null) &&
  @     (other.getCandidateID() == candidateID));
  @*/
	public /*@ pure @*/ boolean sameAs(/*@ non_null @*/ final Candidate other) {
		return (other.getCandidateID() == this.candidateID);
	}

/**
 * How many votes have been received by this round of counting?
 * 
 * @param count The round of counting
 * @return The total number of votes received so far
 */
public /*@ pure @*/ long getTotalAtCount(final int count) {
	long totalAtCount = 0;
	
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
public /*@ pure @*/ boolean isElected() {
	return (getStatus() == ELECTED);
	}
}