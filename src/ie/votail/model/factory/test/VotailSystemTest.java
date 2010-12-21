package ie.votail.model.factory.test;

import java.util.logging.Logger;

import ie.votail.model.Scenario;
import ie.votail.model.VoteTable;
import ie.votail.model.factory.VoteFactory;
import ie.votail.model.factory.ScenarioFactory;
import ie.votail.model.factory.ScenarioList;

import org.testng.annotations.Test;

import election.tally.BallotBox;
import election.tally.BallotCounting;
import election.tally.Constituency;

public class VotailSystemTest {
  @Test
  public void twoCandidateTest() {
    VoteFactory voteFactory = new VoteFactory(
      VoteFactoryTest.MODELS_VOTING_ALS);
    ScenarioFactory scenarioFactory = new ScenarioFactory();
    BallotCounting ballotCounting = new BallotCounting();
    Logger logger = Logger.getLogger(VoteFactory.LOG_FILENAME);
    
    final int candidates = 2;
    final int seats = 1;
    ScenarioList scenarios = scenarioFactory.find(candidates,seats);
    
    for (Scenario scenario: scenarios) {
      logger.info(scenario.toString());
      final int scope = 5;
      VoteTable voteTable = voteFactory.generateVoteTable(scenario, scope);
      Constituency constituency = voteTable.getConstituency();
      logger.info(constituency.toString());
      BallotBox ballotBox = voteTable.getBallotBox();
      logger.info(ballotBox.toString());
      ballotCounting.setup(constituency);
      ballotCounting.load(ballotBox);
      ballotCounting.count();
      logger.info(ballotCounting.getResults());
    }
  }

}
