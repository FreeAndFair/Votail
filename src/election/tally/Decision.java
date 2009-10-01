package election.tally;

/**
 * Decisions taken during the counting of ballots.
 * 
 * @design It is necessary to be able to record any decision which might
 *         influence the order in which votes are counted or transfered.
 * @author Dermot Cochran
 * @copyright 2005-2009 Dermot Cochran
 */
public class Decision extends DecisionStatus {

  /**
   * Maximum number of decision points
   */
  public static final int MAX_DECISIONS = 100;

  /** Type of decision taken */
  /*@ public invariant (decisionTaken == DecisionStatus.EXCLUDE)
    @   || (decisionTaken == DecisionStatus.NO_DECISION)
    @   || (decisionTaken == DecisionStatus.DEEM_ELECTED);
    @*/
  protected /*@ spec_public @*/ byte decisionTaken;

  /** Candidate to which the decision applied */
  /*@ public invariant (candidateID != Ballot.NONTRANSFERABLE) 
    @   || (candidateID == Candidate.NO_CANDIDATE);
    @*/
  protected /*@ spec_public @*/  long candidateID;

  /** Round of counting at which decision was taken */
  //@ public invariant 0 <= atCountNumber;
  protected /*@ spec_public @*/  long atCountNumber;

  /*@ requires candidateIDValue != Ballot.NONTRANSFERABLE;
    @ requires candidateIDValue != Candidate.NO_CANDIDATE; 
    @*/
  public void setCandidate(final int candidateIDValue) {
    candidateID = candidateIDValue;
  }

  //@ requires 0 <= countNumberValue;
  public void setCountNumber(final int countNumberValue) {
    atCountNumber = countNumberValue;
  }

  /*@ requires (decisionType == DecisionStatus.EXCLUDE)
    @   || (decisionType == DecisionStatus.DEEM_ELECTED);
    @*/
  public void setDecisionType(final byte decisionType) {
    decisionTaken = decisionType;
  }

  /*@ assignable decisionTaken, atCountNumber, candidateID;
    @ ensures atCountNumber == 0;
    @ ensures candidateID == Candidate.NO_CANDIDATE;
    @ ensures decisionTaken == DecisionStatus.NO_DECISION;
    @*/
  public Decision() {
    super();
    atCountNumber = 0;
    candidateID = Candidate.NO_CANDIDATE;
    decisionTaken = DecisionStatus.NO_DECISION;
  }
}
