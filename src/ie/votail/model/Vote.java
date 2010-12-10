package ie.votail.model;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;

public class Vote {
  int ballotID;
  int candidateID;
  int ranking;
  
  /**
   * Convert an Alloy Tuple into a Vote
   * 
   * @param tupleSet
   */
  //@ requires tuple.arity() == 3;
  //@ ensures 0 < ranking;
  public Vote(A4Tuple tuple) {
      this.ballotID = Integer.parseInt(tuple.atom(0));
      this.candidateID = Integer.parseInt(tuple.atom(1));
      this.ranking = Integer.parseInt(tuple.atom(2));
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
