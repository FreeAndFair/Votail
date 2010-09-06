package ie.lero.evoting.test.data;

public class Scenario {
  Outcome[] outcomes;
  private int length;

  public Scenario (int numberOfCandidates) {
    outcomes = new Outcome[numberOfCandidates];
    length = numberOfCandidates;
  }
  
  /**
   * Use a seed number to generate a sequence of outcomes
   * 
   * @param seed The generator for the sequence
   */
  public void generate (int seed, int winners) {
    int base = seed;
    for (int i=0; i<winners; i++) {
      outcomes[i] = winner(base);
      base /= Outcome.Radix;
    }
    for (int i=winners; i<length; i++) {
      outcomes[i] = loser(base); 
      base /= Outcome.Radix;
    }
  }

  private Outcome loser(int base) {
    return new Outcome (base, Outcome.SORE_LOSER, Outcome.TIED_LOSER);
  }

  private Outcome winner(int base) {
    return new Outcome(base, Outcome.TIED_WINNER, Outcome.WINNER);
  }
  
  public int getLength() {
    return length;
  }
  
  /** Get the outcome for any integer index, wrapping around if needed
   * 
   * @param n The index
   * @return The candidate outcome
   */
  public Outcome getOutcome (int n) {
    int index = n % length;
    return outcomes[index];
  }
}
