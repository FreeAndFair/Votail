package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;

public class WorkPackage {

  private ElectoralScenario scenario;
  private int candidates;
  private int scope;

  public WorkPackage(ElectoralScenario scenario, int candidates, int scope) {
    this.scenario = scenario;
    this.candidates = candidates;
    this.scope = scope;
  }

  /**
   * @return the scenario
   */
  public ElectoralScenario getScenario() {
    return scenario;
  }

  /**
   * @return the candidates
   */
  public int getCandidates() {
    return candidates;
  }

  /**
   * @return the scope
   */
  public int getScope() {
    return scope;
  }
  
}
