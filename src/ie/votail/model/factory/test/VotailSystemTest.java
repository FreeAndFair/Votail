package ie.votail.model.factory.test;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.util.logging.Logger;

import org.junit.Test;

import election.tally.BallotCounting;
import election.tally.Constituency;

public class VotailSystemTest {
  @Test
  public void twoCandidateTest() {
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOG_FILENAME);
    
    final int candidates = 2;
    final int seats = 1;
    ScenarioList scenarios = scenarioFactory.find(candidates,seats);
    
    for (ElectoralScenario scenario: scenarios) {
      logger.info(scenario.toString());
      final int scope = 5;
      BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
      ElectionConfiguration electionConfiguration 
        = ballotBoxFactory.extractBallots(scenario, scope);
      Constituency constituency = electionConfiguration.getConstituency();
      logger.info(constituency.toString());
      logger.info(electionConfiguration.toString());
      ballotCounting.setup(constituency);
      ballotCounting.load(electionConfiguration);
      ballotCounting.count();
      logger.info(ballotCounting.getResults());
    }
  }
}
