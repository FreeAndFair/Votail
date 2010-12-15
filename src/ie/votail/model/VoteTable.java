package ie.votail.model;

import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import election.tally.BallotBox;

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
  
  /** The number of ballots represented in this table of votes */
  protected int numberOfBallots = 0;
  
  /** The votes */
  protected ArrayList<Vote> votes;
  
  /** The list of ballots identifiers stored in this table */
  protected int[] ballotIDs;

  /**
   * Create a vote table from an Alloy Analyser solution for creation of an
   * electoral scenario.
   * 
   * @param solution The Alloy Analyser solution for an electoral scenario.
   */
  //@ requires solution.satisfiable();
  public VoteTable() {
    
    votes = new ArrayList<Vote>();
    ballotIDs = new int[MAX_BALLOTS];
    
    
  }

  /**
   * Add a <code>vote</code> to this table and update the list of ballots.
   * <p>
   * A <code>ballot</code> is a ranked sequence of votes. A <code>vote</code> 
   * is a tuple consisting of
   * <code>ballotID, ranking</code> and <code>candidateID</code>.
   * 
   * @param vote The <code>vote</code> to be added
   */
  /*@ assignable numberOfBallots;
    @ ensures \old(numberOfBallots) <= numberOfBallots;
    @*/
  public final void add(/*@ non_null*/ final Vote vote) {
    votes.add(vote);
    updateBallotIDs(vote.ballotID);
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
        preferences[ranking] = this.getCandidateID(ballotID,ranking);
      }
      box.accept(preferences);
    }
    return box;
  }

  /**
   * 
   * @param ballotID
   * @param ranking
   * @return
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
   * 
   * @param ballotID
   * @return
   */
  protected int getNumberOfRankings(int ballotID) {
    int count = 0;
    for (Vote vote : votes) {
      if (vote.ballotID == ballotID) {
        count++;
      }
    }
    return count;
  }
}
