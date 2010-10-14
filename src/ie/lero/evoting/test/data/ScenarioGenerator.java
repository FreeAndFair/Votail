package ie.lero.evoting.test.data;

import ie.votail.model.Scenario;

import java.util.logging.Logger;

public class ScenarioGenerator {

  Scenario[] scenarios;
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
    //scenarios = solve (winners, losers);
  }

  /**
   * 
   * @param winners
   * @param losers
   * @return
   */
  public Scenario solve(int winners, int losers) {
    return null;
    // TODO use Alloy API to generate all possible scenaios
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
