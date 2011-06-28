package election.tally;

/**
 * Abstract State Machine for <code>election.tally.Candidate</code> class.
 * 
 * @author Dermot Cochran
 */

public class CandidateStatus {
  
  /** State value for a candidate neither elected nor eliminated yet */
  public static final byte CONTINUING = 0;
  /**
   * State value for a candidate deemed to have been elected either by
   * having a quota or being the highest continuing candidate for the
   * last remaining seat.
   */
  public static final byte ELECTED = 1;
  /**
   * State value for a candidate excluded from election as being one
   * of the lowest continuing candidates at the end of a round of counting.
   */
  public static final byte ELIMINATED = 2;
  
  /** Abstract State Machine (ASM) specification */
  /*@ public invariant state == ELECTED || state == ELIMINATED ||
    @   state == CONTINUING;
    @ public initially state == CONTINUING;
    @ public constraint \old(state) == ELECTED ==> state == ELECTED;
    @ public constraint \old(state) == ELIMINATED ==> state == ELIMINATED;
    @*/
  protected /*@ spec_public @*/ byte state = CONTINUING;
}