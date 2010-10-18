package ie.votail.model;

import java.util.ArrayList;
import java.util.Iterator;

import edu.mit.csail.sdg.alloy4compiler.ast.Expr;

/**
 * A model election scenario is a set of possible outcomes for each candidate. 
 * Each branch in the counting algorithm is associated with at least one
 * such scenario. So, testing all scenarios should achieve full path coverage
 * of the counting system.
 */


public class Scenario {
  private static final int MAX_OUTCOMES = 30;

  private /*@ non_null @*/ ArrayList<Outcome> outcomes;
  
  /*@
   * private invariant 0 <= numberOfOutcomes;
   * private invariant numberOfOutcomes <= MAX_OUTCOMES;
   */
  private int numberOfOutcomes;

  /**
   * Create a new model scenario.
   */
  public Scenario () {
    outcomes = new ArrayList<Outcome>();
    numberOfOutcomes = 0;
  }
  
  /**
   * Textual representation of a model election scenario.
   */
  public String toString() {
    Iterator<Outcome> iterator = outcomes.iterator();
    StringBuffer stringBuffer = new StringBuffer ("scenario (");
    while (iterator.hasNext()) {
      stringBuffer.append(" ");
      stringBuffer.append(iterator.next().toString());
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
   * ensures 1 + \old(numberOfOuctomes) == numberOfOutcomes
   * ensures outcomes.contains(outcome);
   */
  public void addOutcome(/*@ non_null */ Outcome outcome) {
    outcomes.add(outcome);
    numberOfOutcomes++;
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
    Iterator<Outcome> iterator = outcomes.iterator();
    StringBuffer predicateStringBuffer = new StringBuffer("some disj ");
    for (int i=0; i < numberOfOutcomes; i++) {
      if (i > 0 ) {
        predicateStringBuffer.append(", "); 
      }
      predicateStringBuffer.append("c" + i);
    }
    predicateStringBuffer.append(": Candidate | ");
    int i=0;
    while (iterator.hasNext()) {
      if (i > 0 ) {
        predicateStringBuffer.append(" and "); 
      }
      predicateStringBuffer.append("c" + i + ".outcome = " + iterator.next().toString());
      i++;
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
   * Compare two scenarios for the same multiset of outcomes
   * 
   * @param other The other scenario
   * @return Two scenarios are equivalent of they contain the same quantity of
   * each kind of outcome
   */
  /*@
   * 
   */
  public boolean equivalentTo (/*@ non_null*/ Scenario other) {
    return canonical().equals(other.canonical());
  }

  /**
   * Create a scenario with one extra outcome
   * 
   * 
   * @param outcome
   * @return
   */
  /*@
   * 
   */
  public Scenario append(Outcome outcome) {
    Scenario result = this.copy();
    result.addOutcome(outcome);
    return result;
  }

  /**
   * Create a scenario with an equivalent set of outcomes
   * 
   * @return An equivalent scenario
   */
  /*@
   * ensures Result.equivalentTo(this);
   */
  private Scenario copy() {
    Scenario clone = new Scenario();
    Iterator<Outcome> iterator = this.outcomes.iterator();
    while (iterator.hasNext()) {
      clone.addOutcome(iterator.next());
    }
    return clone;
  }

  /**
   * 
   * 
   * @return True if any tied outcomes exist
   */
  public boolean isTied() {
    Iterator<Outcome> iterator = this.outcomes.iterator();
    while (iterator.hasNext()) {
      Outcome outcome = iterator.next();
      if (outcome.isTied()) {
        return true;
      }
    }
    return false;
  }
}
