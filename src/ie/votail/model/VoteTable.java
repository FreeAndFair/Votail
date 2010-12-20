package ie.votail.model;

import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import election.tally.BallotBox;
import election.tally.Candidate;

/**
 * A table of preference votes which can be converted into ballots for 
 * counting.
 * 
 * @author Dermot Cochran
 */
public class VoteTable {
  
  /** The null value for a candidate ID */
  protected static final int NO_CANDIDATE_ID = 0;
  
  /** The maximum expected number of ballots to use when testing the count */
  protected static final int MAX_BALLOTS = 100000;
  
  protected static final int MAX_VOTES = MAX_BALLOTS * Candidate.MAX_CANDIDATES;
  
  /** The number of ballots represented in this table of votes */
  protected int numberOfBallots = 0;
  
  /** The votes */
  protected Vote[] votes;
  
  /** The list of ballots identifiers stored in this table */
  protected int[] ballotIDs;

  protected int numberOfVotes = 0;

  /**
   * Create a vote table.
   */
  public VoteTable() {
    votes = new Vote [MAX_VOTES];
    ballotIDs = new int[MAX_BALLOTS];
  }

  /**
   * Add this ballotID to the list if not already added.
   * 
   * @param ballotID
   */
  protected void updateBallotIDs(int ballotID) {
    for (int i=0; i < numberOfBallots; i++) {
      if (ballotID == ballotIDs[i]) {
        return;
      }
    }
    ballotIDs[numberOfBallots] = ballotID;
    numberOfBallots++;
  }

  /**
   * Convert the table of votes into a ballot box that can be counted
   * 
   * @return The Ballot Box
   */
  public BallotBox getBallotBox() {
    BallotBox box = new BallotBox();
    
    for (int i=0; i < numberOfBallots; i++) {
      int ballotID = ballotIDs[i];
      int numberOfRankings = this.getNumberOfRankings(ballotID);
      int[] preferences = new int[numberOfRankings];
      
      for (int ranking=1; ranking <= numberOfRankings; ranking++) {
        preferences[ranking-1] = this.getCandidateID(ballotID,ranking);
      }
      box.accept(preferences);
    }
    return box;
  }

  /**
   * Get the candidate of given rank on a given ballot
   * 
   * @param ballotID The ballot identifier
   * @param ranking The ranking
   * @return The candidate identifier
   */
  protected int getCandidateID(int ballotID, int ranking) {
    for (Vote vote : votes) {
      if (vote.ballotID == ballotID && vote.ranking == ranking) {
        return vote.candidateID;
      }
    }
    return NO_CANDIDATE_ID;
  }

  /**
   * Get the number of rankings on a given ballot
   * 
   * @param ballotID The ballot identifier
   * @return The number of preferences used
   */
  //@ ensures 0 <= \result;
  protected int getNumberOfRankings(int ballotID) {
    int count = 0;
    for (int index = 0; index < votes.length; index++) {
      if (votes[index] != null) {
        if (votes[index].ballotID == ballotID) {
          count++;
        }
      }
    }
    return count;
  }

  /**
   * Extract the list of ballot identifiers from an Alloy tuple set
   * 
   * @param tupleSet The Alloy tuple set
   */
  public void extractBallotIDs(/*@ non_null */ A4TupleSet tupleSet) {    
    
    for (A4Tuple tuple: tupleSet) {
      int index = getIndex(tuple);
      int ballotID = Integer.parseInt(tuple.atom(1));
      updateBallotIDs(ballotID);
      
      makeVote(index);
      votes[index].setBallotID(ballotID);
    }  
  }

  /**
   * Extract the list of rankings from an Alloy tuple set
   * 
   * @param tupleSet The Alloy tuple set
   */
  public void extractRankings(A4TupleSet tupleSet) {
    for (A4Tuple tuple: tupleSet) {
      
      int index = getIndex(tuple);
      int ranking = Integer.parseInt(tuple.atom(1));
      
      makeVote(index);
      votes[index].setRanking(ranking);
    }
  }

  /**
   * Extract the list of candidate identifiers from an Alloy tuple set
   * 
   * @param tupleSet The Alloy tuple set
   */
  public void extractCandidateIDs(A4TupleSet tupleSet) {

    for (A4Tuple tuple: tupleSet) {
      int index = getIndex(tuple);
      int candidateID = Integer.parseInt(tuple.atom(1));
      
      makeVote(index);
      votes[index].setCandidateID(candidateID);
    }
  }

  /**
   * Get the index number of the vote
   * 
   * @param tuple
   * @return
   */
  protected int getIndex(A4Tuple tuple) {
    return Integer.parseInt(tuple.atom(0).substring(5));
  }

  /**
   * Initialise the vote object if not already created
   * 
   * @param index The position of the vote in the array
   */
//@ require 0 <= index && index < MAX_VOTES;
  protected void makeVote(int index) {
    
    if (votes[index] == null) {
      votes[index] = new Vote();
      numberOfVotes++;
    }
  }
  
  public String toString() {
    StringBuffer buffer = new StringBuffer(numberOfVotes + " votes in " + 
                                           numberOfBallots + " ballots ");
    
    for (int index = 0; index < votes.length; index++) {
      if (votes[index] != null) {
        buffer.append("(" + votes[index] + ") ");
      }
    }
    
    return buffer.toString();
  }
}
