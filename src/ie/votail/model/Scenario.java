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
  private Method method;

  /**
   * Create a new model scenario
   * 
   * @param numberOfWinners
   * @param numberOfCandidates
   */
  /*@
   * requires 1 < numberOfCandidates;
   */
  public Scenario (int numberOfCandidates, Method method) {
    this.method = method;
    outcomes = new Outcome[numberOfCandidates];
  }
 
  /**
   * Create a new scenario which contains these outcomes 
   * 
   * @param outcomes
   */
  public Scenario(/*@ non_null @*/ Outcome[] outcomes, Method method) {
    this.method = method;
    System.arraycopy(outcomes, 0, this.outcomes, 0, outcomes.length);
  }


  public Scenario(Outcome[] combined) {
    // TODO Auto-generated constructor stub
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
  
  /**
   * Create an Alloy predicate expression for this scenario, for example:
   * <p> 
   *   some disj c0,c1,c2,c3,c4,c5,c6,c7,c8: Candidate |
   *     c0.outcome = Winner and 
   *     c1.outcome = QuotaWinner and 
   *     c2.outcome = CompromiseWinner and 
   *     c3.outcome = Loser and
   *     c4.outcome = EarlyLoser and 
   *     c5.outcome = SoreLoser and
   *     c6.outcome = TiedWinner and 
   *     c7.outcome = TiedLoser and 
   *     c8.outcome = TiedEarlyLoser
   * </p>
   * @return The Alloy predicate as a string
   */
  public String toPredicate() {
    StringBuffer predicateStringBuffer = new StringBuffer("some disj ");
    for (int i=0; i < numberOfOutcomes; i++) {
      if (i > 0 ) {
        predicateStringBuffer.append(", "); 
      }
      predicateStringBuffer.append("c" + i);
    }
    predicateStringBuffer.append(": Candidate | ");
    for (int i=0; i < numberOfOutcomes; i++) {
      if (i > 0 ) {
        predicateStringBuffer.append(" and "); 
      }
      predicateStringBuffer.append("c" + i + ".outcome = " + getOutcome(i).toString());
    }
    return predicateStringBuffer.toString();
  }
  
  /**
   * Extend scenario by adding extra outcomes
   * 
   * @param tail
   * @return
   */
  public Scenario add (Scenario tail) {
    Outcome[] combined = new Outcome [this.numberOfOutcomes + tail.numberOfOutcomes];
    for (int i=0; i < this.numberOfOutcomes; i++) {
      combined[i] = this.outcomes[i];
    }
    for (int j=0; j < tail.numberOfOutcomes; j++) {
      combined[j+this.numberOfOutcomes] = tail.outcomes[j];
    }
    
    return new Scenario (canonicalSort(combined));
  }

  private Outcome[] canonicalSort(Outcome[] combined) {
    // TODO Auto-generated method stub
    return null;
  }
}
