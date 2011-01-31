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
  public boolean check(/*@ non_null @*/ Candidate candidate, 
      int threshold) {
    
    // Winners
    if (this == Winner || this == QuotaWinner || this == CompromiseWinner || 
        this == TiedWinner) {
      return candidate.isElected();
    }
    // Non-sore losers
    else if (this == Loser || this == TiedLoser || this == EarlyLoser || 
        this == TiedEarlyLoser) {
        return !candidate.isElected() && threshold <= candidate.getTotalVote();
    }
    // Sore losers
    else if (this == SoreLoser || this == TiedSoreLoser) {
        return candidate.isEliminated() && candidate.getTotalVote() < threshold;
    }
    
    Logger.getAnonymousLogger().warning(
        "Outcome " + this.toString() + " failed to match " + candidate);
    return false;
  }
}
