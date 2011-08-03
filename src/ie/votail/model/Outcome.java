/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model;

import java.util.logging.Logger;

import election.tally.Candidate;

// The names of each outcome must be exactly the same as those in Voting.als
public enum Outcome {
  SoreLoser, EarlySoreLoserNonTransferable, TiedSoreLoser, EarlyLoser,
  EarlyLoserNonTransferable, EarlySoreLoser, Loser, TiedLoser,
  TiedWinner, CompromiseWinner, QuotaWinner, AboveQuotaWinner,
  QuotaWinnerNonTransferable, Winner,
  SurplusWinner, WinnerNonTransferable;
  
  /**
   * Does this outcome require a tie-breaker?
   * 
   * @return <code>True>/code> if it does
   */
  public/*@ pure @*/ boolean isTied() {
    return this == TiedSoreLoser || this == TiedWinner || this == TiedLoser;
  }
  
  /**
   * Verify that candidate's results match the recorded outcome.
   * 
   * @param candidate The candidate to be verified
   * @return True if the results match the outcome
   */
  public boolean check(final /*@ non_null @*/ Candidate candidate,   
      final int threshold, final int quota) {
    
    // Winners above quota, with our without transfers
    if (this == SurplusWinner || this == AboveQuotaWinner ||
        this == WinnerNonTransferable || this == QuotaWinnerNonTransferable) {
      return candidate.isElected() && quota < candidate.getTotalVote();
    }
    // Winner at quota, with or without transfers
    if (this == Winner || this == QuotaWinner) {
      return candidate.isElected() && quota == candidate.getTotalVote();
    }
    // Winners below quota, with or without ties
    if (this == CompromiseWinner || this == TiedWinner) {
      return candidate.isElected() && candidate.getTotalVote() < quota;
    }
    
    // Losers or tied losers of any kind
    if (this == Loser || this == TiedLoser) {
        return !candidate.isElected();
    }
    // Losers at or above threshold, with elimination
    if (this == EarlyLoser || 
        this == EarlyLoserNonTransferable) {
        return !candidate.isElected() && 
               candidate.isEliminated() && 
               threshold <= candidate.getTotalVote();
    }
    // Early Losers below threshold, with or without ties
    if (this == EarlySoreLoserNonTransferable || this == EarlySoreLoser) {
        return !candidate.isElected() && 
               candidate.isEliminated() && 
               candidate.getTotalVote() < threshold;
    }
    // Late Losers below threshold, with or without ties
    if (this == SoreLoser || this == TiedSoreLoser) {
        return !candidate.isElected() && 
               candidate.getTotalVote() < threshold;
    }
    
    Logger.getAnonymousLogger().warning(
        "Outcome " + this.toString() + " failed to match " + candidate);
    return false;
  }
}
