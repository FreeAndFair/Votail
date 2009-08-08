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
public class Decision extends DecisionStatus {
	
/**
	 * Maximum number of decision points 
	 */
public static final int MAX_DECISIONS = 100;
	
/** Type of decision taken */
//@ public initially decisionTaken == NO_DECISION;
/*@ public invariant (decisionTaken == ELECT_BY_QUOTA) ||
  @   (decisionTaken == EXCLUDE) || (decisionTaken == NO_DECISION) || 
  @   (decisionTaken == ROUND_UP_FRACTION) || (decisionTaken == DISTRIBUTE_SURPLUS)
  @   || (decisionTaken == DEEM_ELECTED);
  @ public constraint (\old(decisionTaken) != NO_DECISION) ==>
  @   decisionTaken == \old(decisionTaken);
  @*/
	public byte decisionTaken;
	
/** Candidate to which the decision applied */
//@ public invariant (decisionTaken != NO_DECISION) ==> 0 < candidateID;
//@ public invariant (candidateID != Ballot.NONTRANSFERABLE) || (candidateID == 0);
/*@ public constraint (decisionTaken != NO_DECISION) ==>
  @   candidateID == \old(candidateID);
  @*/
//@ public initially candidateID == 0;	
	public long candidateID;
	
/** Round of counting at which decision was taken */
//@ public invariant 0 <= atCountNumber;
//@ public initially atCountNumber == 0;
/*@ public constraint (decisionTaken != NO_DECISION) ==>
  @   atCountNumber == \old(atCountNumber);
  @*/
	public long atCountNumber;
	
/** Indicates if lots were drawn to make this decision */
/*@ public invariant (decisionTaken == ELECT_BY_QUOTA) ==>
  @   chosenByLot == false;
  @ public constraint (decisionTaken != NO_DECISION) ==>
  @   chosenByLot == \old(chosenByLot);  
  @*/
	public boolean chosenByLot;
	
/**	Default constructor */
/*@ public normal_behavior
  @   ensures decisionTaken == NO_DECISION;
  @   ensures atCountNumber == 0;
  @   ensures candidateID == 0;
  @   ensures chosenByLot == false;
  @*/
	public /*@ pure @*/ Decision(){
		decisionTaken = NO_DECISION;
		atCountNumber = 0;
		candidateID = Candidate.NO_CANDIDATE;
		chosenByLot = false;	
	}
}
