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
   * @param theScenario the scenario to set
   */
  public void setScenario(final ElectoralScenario theScenario) {
    this.scenario = theScenario.canonical();
  }
  /**
   * @param ballotBox the ballotBox to set
   */
  public void setBallots(final Ballot[] ballotsToSet) {
    int numberOfBallots = 0;
    for (int i=0; i < ballotsToSet.length; i++) {
      if (ballotsToSet[i] !=null) {
        numberOfBallots++;
      }
    }
    this.ballots = new Ballot[numberOfBallots];
    int ballot = 0;
    for (int b=0; b < ballotsToSet.length; b++) {
      if (ballotsToSet[b] != null) {
        this.ballots[ballot++] = ballotsToSet[b];
      }
    }
  }
  
}
