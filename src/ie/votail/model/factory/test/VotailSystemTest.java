// 2010-2011, Dermot Cochran, IT University of Copenhagen

package ie.votail.model.factory.test;

import org.testng.Assert;
import org.testng.annotations.Test;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.factory.BallotBoxFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import java.util.logging.Logger;

import election.tally.BallotCounting;
import election.tally.Constituency;

public class VotailSystemTest {
  @Test
  public void prstv(int numberOfSeats) {
    
    final int scope = numberOfSeats;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    logger.info("Using scope = " + scope);
    
    int numberOfFailures = 0;
    int total = 0;
    
    for (int seats = 1; seats <= numberOfSeats; seats++) {
      for (int candidates = 1 + seats; candidates <= 1 + seats * seats; candidates++) {
        
        ScenarioList scenarioList = 
          scenarioFactory.find(candidates, seats, Method.STV);
        
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
          if (!scenario.check(ballotCounting)) {
            logger.severe("Unexpected results for scenario " + scenario
                + " and ballot box " + electionConfiguration);
            numberOfFailures++;
          }
          total++;
        }
      }
    }
    if (0 < numberOfFailures) {
      Assert.fail(numberOfFailures + " failures out of " + total);
    }
  }
  
  public static void main(String [ ] args) {
    VotailSystemTest universalTest = new VotailSystemTest();
    universalTest.plurality(12);
    universalTest.prstv(7);
  }

  protected void plurality(int numberOfCandidates) {
    
    final int scope = numberOfCandidates +1;
    final int seats = 1;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    logger.info("Using scope = " + scope);
    
    int numberOfFailures = 0;
    int total = 0;
    
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; candidates++) {
        
        ScenarioList scenarioList = 
          scenarioFactory.find(candidates, seats, Method.Plurality);
        
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
          ballotCounting.usePlurality();
          ballotCounting.count();
          logger.info(ballotCounting.getResults());
          if (!scenario.check(ballotCounting)) {
            logger.severe("Unexpected results for scenario " + scenario
                + " and ballot box " + electionConfiguration);
            numberOfFailures++;
          }
          total++;
        }
      }
    if (0 < numberOfFailures) {
      Assert.fail(numberOfFailures + " failures out of " + total);
    }
  }
}
