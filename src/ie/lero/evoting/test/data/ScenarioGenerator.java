package ie.lero.evoting.test.data;

import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.Scenario;

import java.util.ArrayList;
import java.util.logging.Logger;

public class ScenarioGenerator {

  ArrayList<Scenario> scenarios;
  int numberOfCandidates;
  int index;
  Logger scenarioLogger;

  /**
   * @param winners
   *        The number of seats that can be won
   * @param losers
   *        The number of other candidates
   */
  /*@
   * requires 0 < winners;
   * requires 0 <= losers;
   */
  public ScenarioGenerator(int winners, int losers) {

    scenarioLogger = Logger.getLogger("scenarios.log");
    
    numberOfCandidates = winners + losers;
    index = 0;

    Outcome[] outcomes = new Outcome[numberOfCandidates];
    
    outcomes[0] = Outcome.WINNER;

    // for intermediate rounds of counting
    for (int round = 1; round < winners; round++) {

      for (Outcome outcome: clearWinners()) {
        
        outcomes[round] = outcome;

        // Last Winner or Winner by tie breaker

        // Loser by tie breaker or Last Loser

        // Other Loser Events

        // Early Loser

        // Sore Loser (below threshold)

        scenarios.add(new Scenario(outcomes,Method.STV));
        
        // Log the current set of outcomes
        scenarioLogger.info(outcomes.toString());
      }
    }
  }

  private ArrayList<Outcome> clearWinners() {
    ArrayList<Outcome> Winners = new ArrayList<Outcome>();
    Winners.add(Outcome.WINNER);
    Winners.add(Outcome.QUOTA_WINNER);
    return Winners;
  }

  public Scenario getScenario(int n) {
    return scenarios[n];
  }

}
