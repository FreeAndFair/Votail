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
          ElectionConfiguration electionConfiguration =
              createElection(scope, ballotCounting, logger, scenario);
          ballotCounting.count();
          logger.info(ballotCounting.getResults());
          if (!scenario.check(ballotCounting)) {
            logFailure(scope, logger, scenario, electionConfiguration);
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

  /**
   * @param scope
   * @param ballotCounting
   * @param logger
   * @param scenario
   * @return
   */
  protected ElectionConfiguration createElection(final int scope,
      BallotCounting ballotCounting, Logger logger, ElectoralScenario scenario) {
    BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
    ElectionConfiguration electionConfiguration =
        ballotBoxFactory.extractBallots(scenario, scope);
    //@ assert electionConfiguration != null;
    //@ assert 0 < electionConfiguration.size();
    Constituency constituency = electionConfiguration.getConstituency();
    logger.info(electionConfiguration.toString());
    ballotCounting.setup(constituency);
    ballotCounting.load(electionConfiguration);
    return electionConfiguration;
  }

  /**
   * @param scope
   * @param logger
   * @param scenario
   * @param electionConfiguration
   */
  protected void logFailure(final int scope, Logger logger,
      ElectoralScenario scenario, ElectionConfiguration electionConfiguration) {
    logger.severe("Unexpected results for scenario " + scenario
        + " using predicate " + scenario.toPredicate()
        + " with scope " + scope
        + " and ballot box " + electionConfiguration);
  }
  
  public static void main(String [ ] args) {
    VotailSystemTest universalTest = new VotailSystemTest();
    universalTest.plurality(12);
    universalTest.prstv(7);
  }

  protected void plurality(int numberOfCandidates) {
    
    final int seats = 1;
    
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(BallotBoxFactory.LOGGER_NAME);
    
    int numberOfFailures = 0;
    int total = 0;
    
      for (int candidates = 1 + seats; candidates <= numberOfCandidates; 
        candidates++) {
        
        final int scope = candidates;
        logger.info("Using scope = " + scope);

        ScenarioList scenarioList = 
          scenarioFactory.find(candidates, seats, Method.Plurality);
        
        for (ElectoralScenario scenario : scenarioList) {
          logger.info(scenario.toString());
          ElectionConfiguration electionConfiguration =
              createElection(scope, ballotCounting, logger, scenario);
          ballotCounting.usePlurality();
          ballotCounting.count();
          logger.info(ballotCounting.getResults());
          if (!scenario.check(ballotCounting)) {
            logFailure(scope, logger, scenario, electionConfiguration);
            numberOfFailures++;
          }
          total++;
        }
      }
    logNumberPassed(logger, numberOfFailures, total);
  }

  /**
   * @param logger
   * @param numberOfFailures
   * @param total
   */
  protected void logNumberPassed(Logger logger, int numberOfFailures,
      int total) {
    logger.severe(total - numberOfFailures + " scenario tests passed out of " + 
        total);
  }
}
