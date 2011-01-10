// 2010-11, Dermot Cochran, IT University of Copenhagen

package ie.votail.model.factory.test;

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
	public void fullSystemsTest() {

		final int scope = 5;

		ScenarioFactory scenarioFactory = new ScenarioFactory();
		BallotCounting ballotCounting = new BallotCounting();
		Logger logger = Logger.getLogger(BallotBoxFactory.LOG_FILENAME);

		for (int candidates = 6; candidates <= 50; candidates++) {
			for (int seats = 3; seats <= 5; seats++) {
				ScenarioList scenarioList = scenarioFactory.find(candidates,
						seats);

				for (ElectoralScenario scenario : scenarioList) {
					logger.info(scenario.toString());
					BallotBoxFactory ballotBoxFactory = new BallotBoxFactory();
					ElectionConfiguration electionConfiguration = ballotBoxFactory
							.extractBallots(scenario, scope);
					Constituency constituency = electionConfiguration
							.getConstituency();
					logger.info(constituency.toString());
					logger.info(electionConfiguration.toString());
					ballotCounting.setup(constituency);
					ballotCounting.load(electionConfiguration);
					ballotCounting.count();
					String results = ballotCounting.getResults();
					logger.info(results);
					// TODO compare results with scenario
				}
			}
		}
	}
}
