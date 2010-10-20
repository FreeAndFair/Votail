/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model;

public enum Outcome {
  SORE_LOSER,
  TIED_SORE_LOSER,
  EARLY_LOSER,
  TIED_EARLY_LOSER,
  LOSER,
  TIED_LOSER,
  TIED_WINNER,
  COMPROMISE_WINNER,
  QUOTA_WINNER,
  WINNER;

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
    return this == TIED_SORE_LOSER || this == TIED_WINNER ||
      this == TIED_LOSER || this == TIED_EARLY_LOSER;
  }
}
