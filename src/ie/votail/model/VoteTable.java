package ie.votail.model;

import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import election.tally.BallotBox;

public class VoteTable {
  
  protected int numberOfBallots = 0;
  protected ArrayList<Vote> votes;

  /**
   * 
   * @param solution
   */
  public VoteTable(A4Solution solution) {
    
    votes = new ArrayList<Vote>();
    
    // Iterate through the solution and add each vote to the table
    for (Sig sig : solution.getAllReachableSigs()) {
      if (sig.label.contains("Vote")) {
        A4TupleSet tupleSet = solution.eval(sig);
        for (A4Tuple tuple : tupleSet) {
          // Tuple should consist of ballotID, candidateID and ranking
          votes.add(new Vote(tuple));
          numberOfBallots++;
        }
      }
    }
  }

  /**
   * 
   * @param vote
   */
  public void add(/*@ non_null*/ Vote vote) {
    votes.add(vote);
    numberOfBallots++;
  }

  /**
   * 
   * @return
   */
  public BallotBox getBallotBox() {
    BallotBox box = new BallotBox();
    
    int[] ballotIDs = this.getBallotIDs();
    
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

  private int getCandidateID(int ballotID, int ranking) {
    // TODO Auto-generated method stub
    return 0;
  }

  private int getNumberOfRankings(int ballotID) {
    // TODO Auto-generated method stub
    return 0;
  }

  private int[] getBallotIDs() {
    // TODO Auto-generated method stub
    return null;
  }

  private int getNumberOfBallots() {
    // TODO Auto-generated method stub
    return 0;
  }

}
