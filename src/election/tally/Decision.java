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
 * State value of decision to declare this candidate elected by
 * reaching the quota
 */	
	public final static byte ELECT_BY_QUOTA = 0;
	
/**
 * State value for decision to eliminate this candidate as the lowest
 * continuing candidate
 */	
	public final static byte EXCLUDE = 1;
	
/**
 * Default state value to indicate that no decision has been taken
 */	
	public final static byte NO_DECISION = 2;
	
/**
 * State value for decision to round up a fractional transfer of votes
 * to this candidate
 */	
	public final static byte ROUND_UP_FRACTION = 3;
	
/**
 * State value for decision to distribute the surplus of this candidate
 */	
	public final static byte DISTRIBUTE_SURPLUS = 4;

/**
 * State value for the decision to deem this candidate elected as one
 * of the highest continuing candidates for the last remaining seats 
 */	
	public final static byte DEEM_ELECTED = 5;
	
/** Type of decision taken */
//@ public initially decisionTaken == NO_DECISION;
/*@ public invariant (decisionTaken == ELECT_BY_QUOTA) ||
  @   (decisionTaken == EXCLUDE) || (decisionTaken == NO_DECISION) || 
  @   (decisionTaken == ROUND_UP_FRACTION) || (decisionTaken == DISTRIBUTE_SURPLUS)
  @   || (decisionTaken == DEEM_ELECTED);
  @ public constraint (\old(decisionTaken) != NO_DECISION) ==>
  @ decisionTaken == \old(decisionTaken);
  @*/
	public byte decisionTaken;
	
/** Candidate to which the decision applied */
//@ public invariant (decisionTaken != NO_DECISION) ==> 0 < candidateID;
//@ public invariant (candidateID != Ballot.NONTRANSFERABLE) || (candidateID = 0);
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
		candidateID = 0;
		chosenByLot = false;	
	}
}
