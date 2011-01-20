// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.model.factory.test;

import org.testng.Assert;
import org.testng.annotations.Test;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.util.logging.Logger;

import election.tally.BallotCounting;
import election.tally.Constituency;

public class VotailSystemTest {
  @Test
  public void universalTest() {
    
    final int scope = 7;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    
    int numberOfFailures = 0;
    
    for (int seats = 1; seats <= 7; seats++) {
      for (int candidates = 1 + seats; candidates <= 1 + seats * seats; candidates++) {
        
        ScenarioList scenarioList = scenarioFactory.find(candidates, seats);
        
        for (ElectoralScenario scenario : scenarioList) {
          logger.info(scenario.toString());
          BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
          ElectionConfiguration electionConfiguration =
              ballotBoxFactory.extractBallots(scenario, scope);
          //@ assert electionConfiguration != null;
          //@ assert 0 < electionConfiguration.size();
          Constituency constituency = electionConfiguration.getConstituency();
          logger.info(electionConfiguration.toString());
          ballotCounting.setup(constituency);
          ballotCounting.load(electionConfiguration);
          ballotCounting.count();
          logger.info(ballotCounting.getResults());
          if (!scenario.matches(ballotCounting)) {
            logger.severe("Unexpected results for scenario " + scenario
                + " and ballot box " + electionConfiguration);
            numberOfFailures++;
          }
        }
      }
    }
    if (0 < numberOfFailures) {
      Assert.fail(numberOfFailures + " mismatched scenarios.");
    }
    assert numberOfFailures == 0;
  }
}
