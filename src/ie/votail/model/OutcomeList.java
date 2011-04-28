package ie.votail.model;

import java.io.Serializable;
import java.util.ArrayList;

/**
 * @author Dermot Cochran
 *
 */
public class OutcomeList implements Serializable {
  /**
   * 
   */
  private static final long serialVersionUID = 163963999839665650L;
  /**
   * 
   */
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