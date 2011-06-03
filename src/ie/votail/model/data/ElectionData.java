package ie.votail.model.data;

import ie.votail.model.ElectoralScenario;

import java.io.Serializable;

import election.tally.Ballot;

public class ElectionData implements Serializable {
  
  /**
   * 
   */
  private static final long serialVersionUID = -8243647007078052844L;
  protected ElectoralScenario scenario;
  protected Ballot[] ballots;
  
  /**
   * @return The electoral scenario
   */
  public /*@ pure @*/ ElectoralScenario getScenario() {
    return scenario;
  }
  /**
   * @return the ballotBox
   */
  public /*@ pure @*/ Ballot[] getBallots() {
    return ballots;
  }
  /**
   * @param scenario the scenario to set
   */
  public void setScenario(ElectoralScenario scenario) {
    this.scenario = scenario;
  }
  /**
   * @param ballotBox the ballotBox to set
   */
  public void setBallots(Ballot[] theBallots) {
    this.ballots = theBallots;
  }
  
}
