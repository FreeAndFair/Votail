package election.tally;

import election.util.UniqueNumber;

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

public class Candidate {
	
/**
 * Maximum expected number of candidates in any one constituency.
 * 
 * @see <a href="http://en.wikipedia.org/wiki/List_of_political_parties_in_the_Republic_of_Ireland">
 * List of political parties in Ireland</a>	
 * 
 * The average number of candidates could be much less.
 */
public static final int MAX_SEATS = 5;
public static final int MAX_MAJOR_PARTIES = 7; // Large enough to contest two or more seats
public static final int MAX_MINOR_PARTIES = 7; // Too small to contest more than one seat
public static final int MAX_INDEPENDENTS = 7;
public static final int MAX_CANDIDATES = (MAX_SEATS * MAX_MAJOR_PARTIES) + MAX_MINOR_PARTIES + MAX_INDEPENDENTS + 1; // Fifty

/** Identifier for the candidate.
 * 
 * <BON>
 * class_chart CANDIDATE_ID
 * inherit VALUE
 * constraints
 *   The internal identifier for each candidate is a non negative number
 * end
 * </BON>
 */
/*@ public invariant 0 <= candidateID;
  @ public invariant (state != UNASSIGNED) ==> 0 < candidateID;
  @ public invariant (\forall Candidate a, b;
  @   a != null && b != null &&
  @   a.state != UNASSIGNED && b.state != UNASSIGNED;
  @   (a.candidateID == b.candidateID) <==> (a == b));
  @ public constraint ((state != UNASSIGNED) && (\old(state) == state)) ==>
  @   candidateID == \old(candidateID);
  @*/
	protected /*@ spec_public @*/ int candidateID;
	
/** Number of votes added at each count */
/*@ public invariant (\forall int i; 0 < i && i < MAXCOUNT;
  @   0 <= votesAdded[i]);
  @ public initially (\forall int i; 0 < i && i < MAXCOUNT;
  @   votesAdded[i] == 0);	
  @ public invariant votesAdded.length == MAXCOUNT;
  @*/
  protected /*@ spec_public non_null @*/ int[] votesAdded;
	
/** Number of votes removed at each count */
/*@ public invariant (\forall int i; 0 < i && i < MAXCOUNT;
  @                                  0 <= votesRemoved[i]);
  @ public initially (\forall int i; 0 < i && i < MAXCOUNT;
  @                                  votesRemoved[i] == 0);
  @ public invariant votesRemoved.length == MAXCOUNT;
  @*/
  protected /*@ spec_public non_null @*/ int[] votesRemoved;

//@ public invariant votesAdded != votesRemoved;
//@ public invariant votesRemoved.owner != null;
//@ public invariant votesAdded.owner != null;
//@ public invariant votesRemoved != votesAdded;
//@ public invariant votesRemoved.owner == votesAdded.owner;
//@ public invariant \typeof(votesRemoved.owner) <: Candidate.class;
	
/** The status of the candidate at the latest count */
/*@ public invariant state == ELECTED || state == ELIMINATED ||
  @   state == CONTINUING || state == UNASSIGNED;
  @ public initially state == UNASSIGNED;
  @*/      
	protected /*@ spec_public @*/ byte state;
	
/** The number of rounds of counting so far */
//@ public invariant 0 <= lastCountNumber;
//@ public initially lastCountNumber == 0;
//@ public constraint \old(lastCountNumber) <= lastCountNumber;
//@ public invariant lastCountNumber < MAXCOUNT;
	protected /*@ spec_public @*/ int lastCountNumber;
	
/** The count number at which the last set of votes were added */
//@ public invariant 0 <= lastSetAddedCountNumber;
//@ public initially lastSetAddedCountNumber == 0;	
/*@ public constraint 
  @   \old(lastSetAddedCountNumber) <= lastSetAddedCountNumber;
  @*/
//@ public invariant lastSetAddedCountNumber <= lastCountNumber;
	protected /*@ spec_public @*/ int lastSetAddedCountNumber;
	
/**
 * Unique random number used to simulate drawing of lots between candidates.
 * 
 * <BON>
 * class_chart RANDOM_NUMBER
 * explanation
 *   "A number chosen so as to simulate the drawing of lots or shuffling of \
 *   ballot papers.  It should be unbiased and fair so as not to favour any \
 *   one candidate over another, and it should be repeatable so that each \
 *   count will give the same results."
 * inherit VALUE
 * constraints
 *   "The random number cannot be changed once it has been assigned";
 *   "No two candidates can have the same random number";
 *   "The election administrator cannot control the value of the random number"
 * end
 */
/*@ public invariant (\forall Candidate a, b;
  @   a != null && b != null &&
  @   a.state != UNASSIGNED && b.state != UNASSIGNED;
  @   (a.randomNumber == b.randomNumber) <==> (a == b));
  @ public constraint (state != UNASSIGNED) ==>
  @   randomNumber == \old(randomNumber); 	
  @*/
  protected /*@ spec_public @*/ int randomNumber;
  //@ ghost int _randomNumber;
	
/** State value for a candidate neither elected nor eliminated yet */
	public static final byte CONTINUING = 0;
	
/**
 * State value for a candidate deemed to have been elected either by
 * having a quota or being the highest continuing candidate for the
 * last remaining seat.  
 */	
	public static final byte ELECTED = 1;
	
/**
 * State value for a candidate excluded from election as being one
 * of the lowest continuing candidates at the end of a round of counting.  
 */	
	public static final byte ELIMINATED = 2;	

/** State value for a candidate object without a valid ID */	
	public static final byte UNASSIGNED = 3;
	
/**
 * State value for a candidate defeated at the last round of the election
 * e.g. the second highest remaining candidate when the last seat is 
 * being filled  
 */	
	public static final byte DEFEATED = 4;	

/**
 * Maximum possible number of counts
 * 
 * @design This value is not set by the legislation; it is chosen so that
 * fixed length arrays can be used in the specification.  
 */	
	public static final int MAXCOUNT = 100;
	
/**
 * Total number of votes this candidate has at any time 
 * 
 * @design This variable was added as to provide easy access from other classes.
 */
	public int total;

	
/**
 * Gets number of votes added or removed in this round count.
 * 
 * @param count This count number
 * @return A positive number if the candidate received transfers or 
 * a negative number if the candidate's surplus was distributed or 
 * the candidate was eliminated and votes transfered to another. 
 * 
 * <BON>
 * query
 *   How many votes have been added or removed in this count round?
 * </BON>
 */	
/*@ 
  @   public normal_behavior
  @   requires state != UNASSIGNED;
  @   requires 0 <= count;
  @   requires count <= lastCountNumber;
  @   requires count < MAXCOUNT;
  @   ensures \result == votesAdded[count] - votesRemoved[count];
  @*/
	public /*@ pure @*/ int getVoteAtCount(int count){
		int sum = 0;
		if(state != UNASSIGNED){
			if(0 <= count && count <= lastCountNumber){
				sum = (votesAdded[count] - votesRemoved[count]);
			}
			return sum;
		} else {
		return 0;
		}
	}
	
/**
 * Total vote recieved by this candidate less transfers to 
 * other candidates.
 * 
 * @return Net total of votes recieved
 */	
/*@ 
  @   public normal_behavior
  @   requires state != UNASSIGNED;
  @   ensures \result == (\sum int i; 0 <= i && i <= lastCountNumber;
  @     ((votesAdded[i]) - (votesRemoved[i])));
  @*/
	public /*@ pure @*/ int getTotalVote() {
		int i = 0;
		int totalVote = 0;
		if (state != UNASSIGNED) {
			while (0 <= i && i <= lastCountNumber) {
				totalVote += (votesAdded[i] - votesRemoved[i]);
				i++;
			}
			return totalVote;
		} else {
			return 0;
		}
	} //@ nowarn Post;
  	
/**
 * Original number of votes received by this candidate before
 * transfers due to elimination or distribution of surplus votes.
 * 
 * @return Gross total of votes received 
 */	
/*@ 
  @   public normal_behavior
  @   requires state != UNASSIGNED;
  @   ensures \result == (\sum int i; 0 <= i && i <=lastCountNumber;
  @     votesAdded[i]); 
  @   ensures 0 <= \result;
  @*/
	public /*@ pure @*/ int getOriginalVote() {
		int total = 0;
		
 		for (int i = 0; i <= lastCountNumber; i++) {
			total += votesAdded[i];
		}
 		 
		return total;
	} //@ nowarn Post;
	
/**
 * Get status at the current round of counting; {@link #ELECTED}, 
 * {@link #ELIMATED} or {@link #CONTINUING} or {@link #UNASSIGNED}
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
  @   requires state != UNASSIGNED;
  @   ensures \result == candidateID;
  @*/	
	public /*@ pure @*/ int getCandidateID() {
		if (state != UNASSIGNED) {
			return candidateID;
		} else {
			return 0;
		}

	}
	
/**
 * This is the default constructor method for a <code>Candidate</code>
 */	
/*@	
  @   public normal_behavior
  @   requires state != UNASSIGNED;
  @*/
  public Candidate(){
    state = UNASSIGNED;
    votesAdded = new int [MAXCOUNT];
    //@ set votesAdded.owner = this;
    votesRemoved = new int [MAXCOUNT];
    //@ set votesRemoved.owner = this;
    randomNumber = UniqueNumber.getUniqueID(); 
    //@ set _randomNumber = randomNumber;
  }

/**
 * Add a number of votes to the candidate's ballot stack.
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
  @   requires lastCountNumber < count;
  @   requires votesAdded[count] == 0;
  @   requires 0 < count & count < MAXCOUNT;
  @   requires (* new bounds precondition added by Patrick and Joe on 25 Jan 2007 *);
  @   requires 0 <= numberOfVotes;
  @   assignable lastCountNumber, votesAdded[count], lastSetAddedCountNumber;
  @   ensures votesAdded[count] == numberOfVotes;
  @   ensures lastCountNumber == count;
  @   ensures lastSetAddedCountNumber == count;
  @*/
  public void addVote(int numberOfVotes, int count){
    if(state == CONTINUING){
      if(lastCountNumber < count && votesAdded[count] == 0){
        votesAdded[count] = numberOfVotes;
        lastCountNumber = count;
        lastSetAddedCountNumber = count;
      }
    }
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
/*@ 
  @   public normal_behavior
  @   requires state == ELIMINATED || state == ELECTED;
  @   requires lastCountNumber < count;
  @   requires votesRemoved[count] == 0;
  @   requires 0 < count & count < MAXCOUNT;
  @   requires 0 <= numberOfVotes;
  @   assignable lastCountNumber, votesRemoved[count];
  @   ensures votesRemoved[count] == numberOfVotes;
  @   ensures lastCountNumber == count;
  @*/
  public void removeVote(final int numberOfVotes, final int count){
        votesRemoved[count] = numberOfVotes;
        lastCountNumber = count;
    }
	
/** 
 * Sets the candidate ID
 * 
 * @param internalID Identification number for this candidate
 * 
 * @design The candidate ID must be assigned by the client object because 
 * the client object must know who the candidate is.
 */
/*@ 
  @   public normal_behavior
  @   requires state == UNASSIGNED;
  @   requires 0 < internalID;
  @   requires (\forall Candidate other; other != null;
  @     other.candidateID != internalID);
  @   assignable state, candidateID;
  @   ensures candidateID == internalID;
  @   ensures state == CONTINUING;
  @*/
	public void setCandidateID(int internalID){
        this.candidateID = internalID;
        state = CONTINUING;
	}
	
/** Declares the candidate to be elected */
/*@ public normal_behavior
  @   requires state == CONTINUING;
  @   assignable state;
  @   ensures state == ELECTED;
  @*/
	public void declareElected(){
		state = ELECTED;
	}
	
/** Declares the candidate to be eliminated */
/*@ public normal_behavior
  @   requires state == CONTINUING;
  @   assignable state;
  @   ensures state == ELIMINATED;
  @*/
	public void declareEliminated(){
		state = ELIMINATED;
	}
	
/**
 * Gets number of votes in last set of votes added
 * 
 * @design In the first round of counting this is the same as
 * the number of first preferences, otherewise it is the most
 * set of votes recieved. The last set of votes recieved are
 * the only votes considered when a surplus is being distributed.
 * 
 * @return The number of votes in the last set added 
 */	
/*@ public normal_behavior
  @   ensures \result == votesAdded[lastSetAddedCountNumber];
  @*/
	public /*@ pure @*/ int getNumberOfVotesInLastSet(){
		int number = votesAdded[lastSetAddedCountNumber];
		return number;
	}

/**
 * Gets the count number at which the last set of votes was added.
 * 
 * @design This is needed to check which ballots are in the last 
 * set added
 * 
 * @see requirement 19, section 7, item 2, page 19
 * 
 * @return The last count number at which votes were added
 */	
/*@ public normal_behavior
  @   ensures \result == lastSetAddedCountNumber;
  @*/
	public /*@ pure @*/ int getLastSetAddedCountNumber(){
		return lastSetAddedCountNumber;
	}	
	
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
  @ requires state != UNASSIGNED;
  @ ensures (\result == true) <==>
  @   (this.randomNumber > other.randomNumber);
  @*/
	public /*@ pure @*/ boolean isAfter(/*@ non_null @*/ Candidate other){
		return (this.randomNumber > other.randomNumber);
	}
	
/**
 * Is this the same candidate?
 * 
 * @return <code>true</code> if this is the same candidate
 */
/*@ ensures \result == ((other != null) && 
  @   (other.getCandidateID() == candidateID));
  @*/
	public /*@ pure @*/ boolean equals(Candidate other) {
		if (other == null) {
			return false;
		}
		return (other.getCandidateID() == this.candidateID);
	}
}