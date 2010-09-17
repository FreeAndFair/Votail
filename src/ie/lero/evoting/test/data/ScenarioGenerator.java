package ie.lero.evoting.test.data;

import java.util.ArrayList;

import ie.votail.model.Method;
import ie.votail.model.Scenario;
import ie.votail.model.Outcome;

public class ScenarioGenerator {

  Scenario[] scenarios;
  int numberOfCandidates;
  int index;

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
    
    numberOfCandidates = winners + losers;
    scenarios = new Scenario[winners+losers];
    index = -1;
  
    createScenarios(winners, losers);
  }

  private void createScenarios(int winners, int losers) {
    nextScenario(winners, losers);
        
    // for intermediate rounds of counting
    for (int round=1, round < winners, round++) {
      
    
      for(Outcome outcome: clearWinners()) {
        scenarios[index].addOutcome (outcome);
    
    // Last Winner
    
    // Winner by tie breaker
    
    // Loser by tie breaker
    
    // Last Loser
    
    // Other Loser Events
    
    // Early Loser
    
    // Sore Loser (below threshold)
    
      
    }
    }
  }

  private void nextScenario(int winners, int losers) {
    index++;
    scenarios[index] = new Scenario(winners+losers);
    scenarios[index].addOutcome(Outcome.WINNER);
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
