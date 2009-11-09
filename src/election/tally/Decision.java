package election.tally;

/**
 * Decisions taken during the counting of ballots.
 * 
 * <p> It is necessary to be able to record any decision which might
 *         influence the order in which votes are counted or transfered.
 * @author Dermot Cochran
 */
public class Decision extends DecisionStatus {

  /**
   * Maximum number of decision points
   */
  public static final int MAX_DECISIONS = 100;

  /** Decision status */
  /*@ public invariant (decisionTaken == DecisionStatus.EXCLUDE)
    @   || (decisionTaken == DecisionStatus.NO_DECISION)
    @   || (decisionTaken == DecisionStatus.DEEM_ELECTED);
    @*/
  protected /*@ spec_public @*/ byte decisionTaken = DecisionStatus.NO_DECISION;

  /** Candidate to which the decision applied */
  /*@ public invariant 0 <= candidateID;
    @*/
  protected /*@ spec_public @*/  long candidateID = Candidate.NO_CANDIDATE;

  /** Round of counting at which decision was taken */
  //@ public invariant 0 <= atCountNumber;
  //@ public initially atCountNumber == 0;
  protected /*@ spec_public @*/  long atCountNumber = 0;

  /*@ requires candidateIDValue != Ballot.NONTRANSFERABLE;
    @ requires candidateIDValue != Candidate.NO_CANDIDATE; 
    @ requires 0 <= candidateIDValue;
    @ assignable candidateID;
    @ ensures getCandidateID() == candidateIDValue;
    @*/
  public void setCandidate(final long candidateIDValue) {
    candidateID = candidateIDValue;
  }

  //@ requires 0 <= countNumberValue;
  //@ assignable atCountNumber;
  //@ ensures getCountNumber() == countNumberValue;
  public void setCountNumber(final long countNumberValue) {
    atCountNumber = countNumberValue;
  }

  /*@ requires (decisionType == DecisionStatus.EXCLUDE)
    @   || (decisionType == DecisionStatus.DEEM_ELECTED);
    @ assignable decisionTaken;
    @ ensures getDecisionStatus() == decisionType;
    @*/
  public void setDecisionType(final byte decisionType) {
    decisionTaken = decisionType;
  }

  //@ ensures \result == decisionTaken;
  public /*@ pure @*/ byte getDecisionStatus() {
    return decisionTaken;
  }

  //@ ensures \result == candidateID;
  public /*@ pure @*/ long getCandidateID() {
    return candidateID;
  }

  //@ ensures \result == atCountNumber;
  public /*@ pure @*/ long getCountNumber() {
    return atCountNumber;
  }

  /*@ requires 0 <= decision.getCountNumber();
    @ requires (decision.getDecisionStatus() == DecisionStatus.EXCLUDE)
    @   || (decision.getDecisionStatus() == DecisionStatus.DEEM_ELECTED);
    @ requires decision.getCandidateID() != Ballot.NONTRANSFERABLE;
    @ requires decision.getCandidateID() != Candidate.NO_CANDIDATE; 
    @ assignable candidateID;
    @ assignable atCountNumber;
    @ assignable decisionTaken;
    @*/
  public void copy(final /*@ non_null @*/ Decision decision) {
      setCountNumber(decision.getCountNumber());
      setCandidate(decision.getCandidateID());
      setDecisionType(decision.getDecisionStatus());
  }
}
