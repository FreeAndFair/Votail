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
      return isWinnerAboveQuota(candidate, quota);
    }
    // Winner at quota, with or without transfers
    if (this == Winner || this == QuotaWinner) {
      return isWinnerAtQuota(candidate, quota);
    }
    // Winners below quota, with or without ties
    if (this == CompromiseWinner || this == TiedWinner) {
      return isWinnerBelowQuota(candidate, quota);
    }
    // Losers at or above threshold, without elimination
    if (this == Loser || this == TiedLoser) {
        return isLoser(candidate, threshold);
    }
    // Losers at or above threshold, with elimination
    if (this == EarlyLoser || 
        this == EarlyLoserNonTransferable) {
        return isEarlyLoser(candidate, threshold);
    }
    // Early Losers below threshold, with or without ties
    if (this == EarlySoreLoserNonTransferable || this == EarlySoreLoser) {
        return isEarlySoreLoser(candidate, threshold);
    }
    // Late Losers below threshold, with or without ties
    if (this == SoreLoser || this == TiedSoreLoser) {
        return isSoreLoser(candidate, threshold);
    }
    
    Logger.getAnonymousLogger().warning(
        "Outcome " + this.toString() + " failed to match " + candidate);
    return false;
  }

  /**
   * @param candidate
   * @param threshold
   * @return
   */
  protected boolean

  /**
   * @param candidate
   * @param threshold
   * @return
   */
  protected b

  /**
   * @param candidate
   * @param threshold
   * @return
   */
  protected boolea

  /**
   * @param candidate
   * @param thresho

  /**
   * @param c

  /**
   * @param candi

  /**
   * @param candidate
   * @param quota
   * @return
   */
  protected boolean isWinnerAboveQuota(final Candidate candidate,
      final int quota) {
    return candidate.isElected() && quota < candidate.getTotalVote();
  }date
   * @param quota
   * @return
   */
  protected boolean isWinnerAtQuota(final Candidate candidate, final int quota) {
    return candidate.isElected() && quota == candidate.getTotalVote();
  }andidate
   * @param quota
   * @return
   */
  protected boolean isWinnerBelowQuota(final Candidate candidate,
      final int quota) {
    return candidate.isElected() && candidate.getTotalVote() < quota;
  }ld
   * @return
   */
  protected boolean isLoser(final Candidate candidate, final int threshold) {
    return !candidate.isElected() &&
           threshold <= candidate.getTotalVote();
  }n isEarlyLoser(final Candidate candidate, final int threshold) {
    return !candidate.isElected() && 
           candidate.isEliminated() && 
           threshold <= candidate.getTotalVote();
  }oolean isEarlySoreLoser(final Candidate candidate,
      final int threshold) {
    return !candidate.isElected() && 
           candidate.isEliminated() && 
           candidate.getTotalVote() < threshold;
  } isSoreLoser(final Candidate candidate, final int threshold) {
    return !candidate.isElected() && 
           !candidate.isEliminated() && 
           candidate.getTotalVote() < threshold;
  }
}
