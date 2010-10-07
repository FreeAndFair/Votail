package ie.lero.evoting.test.data;

import ie.votail.model.Method;
import ie.votail.model.Outcome;
import ie.votail.model.Scenario;

import java.util.ArrayList;
import java.util.logging.Logger;

public class ScenarioGenerator {

  Scenario[] scenarios;
  int numberOfCandidates;
  int index;
  Logger scenarioLogger;
  private int numberOfScenarios;

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

      fillOutcomes(winners, outcomes, round);
    }
  }
  
  // Solve the possible solutions for W winners and L losers, recursively
  public Outcome[] solve (int winners, int losers) {
    return null;
    
  }

  /**
   * Use a recursive method to fill and find the outcomes
   * 
   * @param winners
   * @param outcomes
   * @param round
   */
  public void fillOutcomes(int winners, Outcome[] outcomes, int round) {
      

      // Last Winner or Winner by tie breaker
      
      for (int i = winners; i < numberOfCandidates; i++) {

        outcomes[i] = addLoserOutcome();
     

      //scenarios.add(new Scenario(outcomes,Method.STV));
      numberOfScenarios++;
      }
      
      // Log the current set of outcomes
      scenarioLogger.info(outcomes.toString());
    }

  private Outcome addLoserOutcome() {
    // TODO Auto-generated method stub
    // Loser by tie breaker or Last Loser

    // Other Loser Events

    // Early Loser

    // Sore Loser (below threshold)
    return null;
  }

  /**
   * 
   * @param n
   * @return
   */
  /*@
   * requires 0 <= n;
   * requires n <= scenarios.length;
   */
  public Scenario getScenario(int n) {
    return scenarios[n];
  }

}
