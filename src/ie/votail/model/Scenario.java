package ie.votail.model;

/**
 * A model election scenario is a set of possible outcomes for each candidate. 
 * Each branch in the counting algorithm is associated with at least one
 * such scenario. So, testing all scenarios should achieve full path coverage
 * of the counting system.
 */


public class Scenario {
  private Outcome[] outcomes;
  private int numberOfOutcomes;

  /**
   * Create a new model scenario
   * 
   * @param numberOfWinners
   * @param numberOfCandidates
   */
  /*@
   * requires 1 < numberOfCandidates;
   */
  public Scenario (int numberOfCandidates) {
    outcomes = new Outcome[numberOfCandidates];
  }
 
  
  /** Get the outcome for any integer index
   * 
   * @param index The index
   * @return The candidate outcome
   */
  /*@
   * requires 0 <= index;
   * requires index < numberOfOutcomes;
  */
  public Outcome getOutcome (int index) {
    return outcomes[index];
  }
  
  /**
   * Textual representation of a model election scenario.
   */
  public String toString() {
    StringBuffer stringBuffer = new StringBuffer ("scenario (");
    for (int i=0; i<numberOfOutcomes; i++) {
      if (0 < i) {
        stringBuffer.append(", ");
      }
      stringBuffer.append(outcomes[i].toString());
    }
    stringBuffer.append(")");
    return stringBuffer.toString();
  }
   
  /**
   * Add a candidate outcome to this scenario.
   * 
   * @param outcome The candidate outcome to be added to this scenario
   */
  /*@
   * requires numberOfOutcomes < Outcomes.length;
   */
  public void addOutcome(Outcome outcome) {
    outcomes[numberOfOutcomes++] = outcome;    
  }
}
