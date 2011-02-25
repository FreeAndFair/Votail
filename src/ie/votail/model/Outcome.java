/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model;

import java.util.logging.Logger;

import election.tally.Candidate;

// The names of each outcome must be exactly the same as those in Voting.als
public enum Outcome {
  SoreLoser, SoreLoserNonTransferable, TiedSoreLoser, EarlyLoser,
  EarlyLoserNonTransferable, TiedEarlyLoser, Loser, TiedLoser,
  TiedWinner, CompromiseWinner, QuotaWinner, AboveQuotaWinner,
  QuotaWinnerNonTransferable, Winner,
  SurplusWinner, WinnerNonTransferable;
  
  /**
   * Does this outcome require a tie-breaker?
   * 
   * @return <code>True>/code> if it does
   */
  public/*@ pure @*/ boolean isTied() {
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
      int threshold, int quota) {
    
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
    // Losers at or above threshold, with or without elimination
    else if (this == Loser || this == TiedLoser || this == EarlyLoser || 
        this == TiedEarlyLoser || this == EarlyLoserNonTransferable) {
        return !candidate.isElected() && threshold <= candidate.getTotalVote();
    }
    // Losers below threshold, with or without ties
    else if (this == SoreLoser || this == TiedSoreLoser ||
        this == SoreLoserNonTransferable) {
        return candidate.isEliminated() && candidate.getTotalVote() < threshold;
    }
    
    Logger.getAnonymousLogger().warning(
        "Outcome " + this.toString() + " failed to match " + candidate);
    return false;
  }
}
