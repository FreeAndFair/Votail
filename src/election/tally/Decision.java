package election.tally;

/**
 * Decisions taken during the counting of ballots.
 * 
 * @design It is necessary to be able to record any decision which might
 * influence the order in which votes are counted or transfered. 
 *
 * @author Dermot Cochran
 * @copyright 2005-2009 Dermot Cochran
 */
public class Decision {
	
/**
	 * Maximum number of decision points 
	 */
public static final int MAX_DECISIONS = 100;
	
/** Type of decision taken */
//@ public initially decisionTaken == DecisionStatus.NO_DECISION;
/*@ public invariant (decisionTaken == DecisionStatus.EXCLUDE)
  @   || (decisionTaken == DecisionStatus.NO_DECISION)
  @   || (decisionTaken == DecisionStatus.DEEM_ELECTED);
  @ public constraint (\old(decisionTaken) != DecisionStatus.NO_DECISION) ==>
  @   decisionTaken == \old(decisionTaken);
  @*/
	public byte decisionTaken;
	
/** Candidate to which the decision applied */
/*@ public invariant (decisionTaken == DecisionStatus.NO_DECISION) 
  @   <==> (candidateID == Candidate.NO_CANDIDATE);
  @ public invariant (candidateID != Ballot.NONTRANSFERABLE) 
  @   || (candidateID == Candidate.NO_CANDIDATE);
  @ public constraint (decisionTaken != DecisionStatus.NO_DECISION) ==>
  @   candidateID == \old(candidateID);
  @ public initially candidateID == Candidate.NO_CANDIDATE;
  @*/	
	public long candidateID;
	
/** Round of counting at which decision was taken */
//@ public invariant 0 <= atCountNumber;
//@ public initially atCountNumber == 0;
/*@ public constraint (decisionTaken != DecisionStatus.NO_DECISION) ==>
  @   atCountNumber == \old(atCountNumber);
  @*/
	public long atCountNumber;
	
/**	Default constructor */
/*@ public normal_behavior
  @   assignable decisionTaken, atCountNumber, candidateID;
  @   ensures decisionTaken == DecisionStatus.NO_DECISION;
  @   ensures atCountNumber == 0;
  @   ensures candidateID == Candidate.NO_CANDIDATE;
  @*/
	public Decision() {
		decisionTaken = DecisionStatus.NO_DECISION;
		atCountNumber = 0;
		candidateID = Candidate.NO_CANDIDATE;
	}
}
