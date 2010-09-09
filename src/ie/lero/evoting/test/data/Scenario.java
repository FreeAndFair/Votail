package ie.lero.evoting.test.data;

import election.tally.Candidate;

public class Scenario {
  Candidate[] winners;
  Candidate[] losers;
  Outcome[] outcomes;
  private int length;

  public Scenario (int numberOfCandidates) {
    outcomes = new Outcome[numberOfCandidates];
    length = numberOfCandidates;
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
