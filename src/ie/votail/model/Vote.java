package ie.votail.model;

public class Vote {
  int ballotID;
  int candidateID;
  int ranking;
  
  public int getBallotID() {
    return ballotID;
  }
  public void setBallotID(int ballotID) {
    this.ballotID = ballotID;
  }
  public int getCandidateID() {
    return candidateID;
  }
  public void setCandidateID(int candidateID) {
    this.candidateID = candidateID;
  }
  public int getRanking() {
    return ranking;
  }
  public void setRanking(int ranking) {
    this.ranking = ranking;
  }

  //@ invariant 0 < ranking;
}
