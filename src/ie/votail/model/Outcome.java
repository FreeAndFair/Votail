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
   * Does this outcome require a tie?
   * 
   * @return <code>True>/code> if it does
   */
  public /*@ pure */ boolean isTied() {
    return this == TIED_SORE_LOSER || this == TIED_WINNER ||
      this == TIED_LOSER || this == TIED_EARLY_LOSER;
  }
}
