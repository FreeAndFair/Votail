package ie.votail.model;

import java.util.ArrayList;

/**
 * @author Dermot Cochran
 *
 */
public class OutcomeList {
  private ArrayList<Outcome> outcomes;

  /**
   * 
   */
  public OutcomeList() {
    this.outcomes = new ArrayList<Outcome>();
  }

  /**
   * 
   * @return
   */
  public ArrayList<Outcome> getOutcomes() {
    return outcomes;
  }

  /**
   * 
   * @param outcome
   */
  public void add(final Outcome outcome) {
    this.outcomes.add(outcome);
  }
}