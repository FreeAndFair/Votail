package ie.votail.model;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

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
  protected List<Outcome> outcomes;

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
  public List<Outcome> getOutcomes() {
    return outcomes;
  }

  /**
   * 
   * @param outcome
   */
  public void add(final Outcome outcome) {
    this.outcomes.add(outcome);
  }

  /**
   * @param outcomes the outcomes to set
   */
  public void setOutcomes(final List<Outcome> outcomes) {
    this.outcomes = outcomes;
  }
}