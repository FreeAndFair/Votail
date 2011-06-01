package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;

import java.io.Serializable;

import election.tally.BallotBox;

public class TestData implements Serializable {
  
  protected ElectoralScenario scenario;
  protected BallotBox ballotBox;
  /**
   * @return the scenario
   */
  public ElectoralScenario getScenario() {
    return scenario;
  }
  /**
   * @return the ballotBox
   */
  public BallotBox getBallotBox() {
    return ballotBox;
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
  public void setBallotBox(BallotBox ballotBox) {
    this.ballotBox = ballotBox;
  }
  
}
