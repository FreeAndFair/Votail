package ie.votail.model;

import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;

public class Vote {
  protected /*@ spec_public*/ int ballotID;
  protected /*@ spec_public*/ int candidateID;
  
  /** Relative preference for candidate; 1=first, 2=second, ... */
  //@ public invariant 0 < ranking;
  protected /*@ spec_public*/ int ranking;
  
  /**
   * Convert an Alloy Tuple into a Vote
   * 
   * @param tupleSet
   */
  //@ requires tuple.arity() == 3;
  //@ ensures 0 < ranking;
  public Vote() {
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
  public void setBallotID(int theBallotID) {
    this.ballotID = theBallotID;
    
  }
  public void setCandidateID(int candidateID) {
    this.candidateID = candidateID;
  }
  public void setRanking(int ranking) {
    this.ranking = ranking;
  }

  
}
