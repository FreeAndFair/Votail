/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model;

import java.util.logging.Logger;

import election.tally.Candidate;

// The names of each outcome must be exactly the same as those in Voting.als
public enum Outcome {
  SoreLoser, TiedSoreLoser, EarlyLoser, TiedEarlyLoser, Loser, TiedLoser,
  TiedWinner, CompromiseWinner, QuotaWinner, Winner;
  
  /**
   * Does this outcome require a tie-breaker?
   * 
   * @return <code>True>/code> if it does
   */
  /*@ ensures \result <==> (this == TIED_SORE_LOSER || this == TIED_WINNER ||
   *    this == TIED_LOSER || this == TIED_EARLY_LOSER) 
   */
  public/*@ pure */boolean isTied() {
    return this == TiedSoreLoser || this == TiedWinner || this == TiedLoser
        || this == TiedEarlyLoser;
  }
  
  /**
   * Verify that candidate's results match the recorded outcome.
   * 
   * @param candidate The candidate to be verified
   * @return True if the results match the outcome
   */
  //@ requires (0 <= threshold) && (threshold <= quota);
  //@ requires 0 <= lastRound;
  public boolean matches(/*@ non_null*/Candidate candidate, int quota,
      int threshold, int lastRound) {
    
    if (this == Winner && quota <= candidate.getInitialVote()) {
      return true;
    }
    else if (this == QuotaWinner && quota <= candidate.getOriginalVote()
        && candidate.getInitialVote() < quota) {
      return true;
    }
    else if ((this == CompromiseWinner || this == TiedWinner)
        && candidate.isElected() && candidate.getOriginalVote() < quota) {
      return true;
    }
    else if ((this == Loser || this == TiedLoser) && candidate.isEliminated()
        && threshold <= candidate.getFinalVote()
        && lastRound == candidate.getLastRound()) {
      return true;
    }
    else if ((this == EarlyLoser || this == TiedEarlyLoser)
        && candidate.isEliminated() && threshold <= candidate.getFinalVote()
        && candidate.getLastRound() < lastRound) {
      return true;
    }
    else if ((this == SoreLoser || this == TiedSoreLoser)
        && candidate.isEliminated() && candidate.getFinalVote() < threshold) {
      return true;
    }
    
    Logger.getAnonymousLogger().warning("Outcome " + this.toString() + " failed to match candidate " + candidate + " for quota " + quota +
        " and threshold " + threshold);
    return false;
  }
}
