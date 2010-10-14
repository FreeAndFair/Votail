package ie.votail.model;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;

/**
 * A model election scenario is a set of possible outcomes for each candidate. 
 * Each branch in the counting algorithm is associated with at least one
 * such scenario. So, testing all scenarios should achieve full path coverage
 * of the counting system.
 */


public class Scenario {
  private static final int MAX_OUTCOMES = 30;

  private /*@ non_null @*/ Outcome[] outcomes;
  
  /*@
   * private invariant 0 <= numberOfOutcomes;
   * private invariant numberOfOutcomes <= MAX_OUTCOMES;
   */
  private int numberOfOutcomes;

  /**
   * Create a new model scenario.
   */
  public Scenario () {
    numberOfOutcomes = 0;
    outcomes = new Outcome[MAX_OUTCOMES];
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
   * Sort the candidate outcomes events from highest Winner to lowest Loser
   * 
   * @param unsorted
   * @return
   */
  /*@
   * 
   */
  public Scenario canonical () {
    Scenario sorted = new Scenario();
    // TODO
    return sorted;
  }
  
  /**
   * 
   * @param other
   * @return
   */
  /*@
   * 
   */
  public boolean equivalent (/*@ non_null*/ Scenario other) {
    return canonical().equals(other.canonical());
  }
  
  //TODO equality of length and outcomes
}
