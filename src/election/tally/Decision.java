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
    @ public constraint (\old(decisionTaken) != DecisionStatus.NO_DECISION) ==>
    @   decisionTaken == \old(decisionTaken);
    @*/
  public byte             decisionTaken;

  /** Candidate to which the decision applied */
  /*@ public invariant (decisionTaken == DecisionStatus.NO_DECISION) 
    @   <==> (candidateID == Candidate.NO_CANDIDATE);
    @ public invariant (candidateID != Ballot.NONTRANSFERABLE) 
    @   || (candidateID == Candidate.NO_CANDIDATE);
    @ public constraint (decisionTaken != DecisionStatus.NO_DECISION) ==>
    @   candidateID == \old(candidateID);
    @*/
  public long             candidateID;

  /** Round of counting at which decision was taken */
  //@ public invariant 0 <= atCountNumber;
  /*@ public constraint (decisionTaken != DecisionStatus.NO_DECISION) ==>
    @   atCountNumber == \old(atCountNumber);
    @*/
  public long             atCountNumber;

  /**
   * Create a new decision event.
   * 
   * @param decisionType
   *        Type of decision made e.g. elect or eliminate
   * @param candidateIDValue
   *        ID of the candidate in question
   * @param countNumberValue
   *        Count number in which the decision was made
   */
  /*@ public normal_behavior
    @   requires (decisionType == DecisionStatus.EXCLUDE) ||
    @            (decisionType == DecisionStatus.DEEM_ELECTED);
    @   requires 0 < countNumberValue;
    @   requires candidateID != Candidate.NO_CANDIDATE;
    @   requires candidateID != Ballot.NONTRANSFERABLE;
    @   assignable decisionTaken, atCountNumber, candidateID;
    @   ensures decisionTaken == decisionType;
    @   ensures atCountNumber == countNumberValue;
    @   ensures candidateID == candidateIDValue;
    @*/
  public Decision(final int countNumberValue, final int candidateIDValue,
      final byte decisionType) {
    super();
    decisionTaken = decisionType;
    atCountNumber = countNumberValue;
    candidateID = candidateIDValue;
    /*@ assert (decisionTaken == DecisionStatus.EXCLUDE) ||
      @        (decisionTaken == DecisionStatus.DEEM_ELECTED);
      @*/
  }

  public Decision() {
    super();
    atCountNumber = 0;
    candidateID = Candidate.NO_CANDIDATE;
    decisionTaken = DecisionStatus.NO_DECISION;
  }
}
