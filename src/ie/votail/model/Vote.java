package ie.votail.model;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;

public class Vote {
  int ballotID;
  int candidateID;
  int ranking;
  
  public Vote(ExprVar atom) {
    String voteString = atom.toString();
    // TODO
  }
  public int getBallotID() {
    return ballotID;
  }
  public int getCandidateID() {
    return candidateID;
  }
  
  /*@
   * ensures 0 < \result;
   */
  public int getRanking() {
    return ranking;
  }

  
}
