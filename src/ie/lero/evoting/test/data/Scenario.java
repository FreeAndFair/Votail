package ie.lero.evoting.test.data;

import election.tally.BallotBox;
import election.tally.Candidate;

public class Scenario {
  private Candidate[] winners;
  private Candidate[] losers;
  private Outcome[] outcomes;  
  private Method method; // Voting scheme
  //@ public invariant 0 <= threshold;
  private /*@ spec_public @*/ int threshold;
  private /*@ spec_public @*/ int quota;

  /**
   * 
   * @param numberOfWinners
   * @param numberOfCandidates
   */
  /*@
   * requires numberOfWinners < numberOfCandidates;
   * requires 0 < numbersOfWinners;
   */
  public Scenario (Method methodToUse,int numberOfWinners, int numberOfCandidates) {
    int numberOfLosers = numberOfCandidates - numberOfWinners;
    outcomes = new Outcome[numberOfCandidates];
    winners = new Candidate[numberOfWinners];
    losers = new Candidate[numberOfLosers];
    this.method = methodToUse;
  }
 
  
  /** Get the outcome for any integer index, wrapping around if needed
   * 
   * @param index The index
   * @return The candidate outcome
   */
  /*@
   * requires 0 <= index;
   * requires index < outcomes.length;
  */
  public Outcome getOutcome (int index) {
    return outcomes[index];
  }
  
  /**
   * 
   * @param box
   * @param numberOfSeats
   */
  /*@
   * requires method = Method.STV;
   * requires 0 < numberOfSeats;
   */
  public void setQuota (BallotBox box, int numberOfSeats) {
    
  }
  
  /**
   * 
   * @param box
   * @param percentage
   */
  /*@
   * requires 0 <= percentage;
   */
  public void setThreshold (BallotBox box, int percentage) {
    
  }
  
  public String toString() {
    return "Outcomes: " + outcomes.toString();
    
  }
}
