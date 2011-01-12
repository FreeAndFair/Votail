/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model;

import election.tally.Candidate;

// The names of each outcome must be exactly the same as those in Voting.als
public enum Outcome {
  SoreLoser,
  TiedSoreLoser,
  EarlyLoser,
  TiedEarlyLoser,
  Loser,
  TiedLoser,
  TiedWinner,
  CompromiseWinner,
  QuotaWinner,
  Winner;

  /**
   * Does this outcome require a tie-breaker?
   * 
   * @return <code>True>/code> if it does
   */
  /*@
   * ensures \result <==> (this == TIED_SORE_LOSER || this == TIED_WINNER ||
   *  this == TIED_LOSER || this == TIED_EARLY_LOSER) 
   */
  public /*@ pure */ boolean isTied() {
    return this == TiedSoreLoser || this == TiedWinner ||
      this == TiedLoser || this == TiedEarlyLoser;
  }

  /**
   * Verify that candidate's results match the recorded outcome
   * 
   * @param candidate The candidate to be verified
   * @return True if the results match the outcome
   */
  //@ requires (0 <= threshold) && (threshold <= quota);
public boolean matches(/*@ non_null*/ Candidate candidate, 
    int quota, int threshold) {

    if (this == Winner && quota <= candidate.getOriginalVote()) {
        return true;
    }
    else if (this == Loser && candidate.isEliminated() && 
      threshold <= candidate.getFinalVote()) {
        return true;
    }
        
    return false;
}
}
