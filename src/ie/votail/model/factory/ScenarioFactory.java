/**
 * Find all PR-STV scenarios that match a fixed number of candidate outcomes.
 * 
 * @author Dermot Cochran, 2010, IT University of Copenhagen
 */

package ie.votail.model.factory;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;

import java.util.Iterator;

public class ScenarioFactory {
  
  /**
   * Find all election scenarios for a given number of outcomes
   * 
   * @param numberOfOutcomes The number of candidate outcomes
   * @return All election scenarios with this number of outcomes
   */
  /*@
   * requires 1 < numberOfOutcomes;
   * ensures (numberOfOutcomes == 2) ==> (4 == \result.size());
   * ensures (numberOfOutcomes == 3) ==> (26 == \result.size());
   */
  public /*@ pure */ ScenarioList find(int numberOfOutcomes) {
    ScenarioList scenarios = new ScenarioList();
    if (numberOfOutcomes == 2) {
      
      // Winner gets majority of votes, loser reaches threshold
      Scenario commonScenario = new Scenario();
      commonScenario.addOutcome(Outcome.WINNER);
      commonScenario.addOutcome(Outcome.LOSER);
      scenarios.add(commonScenario);
      
      // Winner by tie breaker, loser reaches threshold
      Scenario tiedScenario = new Scenario();
      tiedScenario.addOutcome(Outcome.TIED_WINNER);
      tiedScenario.addOutcome(Outcome.TIED_LOSER);
      scenarios.add(tiedScenario);
      
      // Winner by tie breaker, loser below threshold
      Scenario landslideScenario = new Scenario();
      landslideScenario.addOutcome(Outcome.WINNER);
      landslideScenario.addOutcome(Outcome.SORE_LOSER);
      scenarios.add(landslideScenario);
      
      // Winner by tie breaker, loser below threshold
      Scenario unusualScenario = new Scenario();
      unusualScenario.addOutcome(Outcome.TIED_WINNER);
      unusualScenario.addOutcome(Outcome.TIED_SORE_LOSER);
      scenarios.add(unusualScenario);
    }
    else {
      // Extend the base scenario by adding one additional candidate outcome
      ScenarioList baseScenarios = find (numberOfOutcomes-1);
      Iterator<Scenario> iterator = baseScenarios.iterator();
      while (iterator.hasNext()) {
        Scenario baseScenario = iterator.next();
        scenarios.add(baseScenario.append(Outcome.WINNER));
        scenarios.add(baseScenario.append(Outcome.QUOTA_WINNER));
        scenarios.add(baseScenario.append(Outcome.COMPROMISE_WINNER));
        scenarios.add(baseScenario.append(Outcome.LOSER));
        scenarios.add(baseScenario.append(Outcome.EARLY_LOSER));
        scenarios.add(baseScenario.append(Outcome.SORE_LOSER));
        // Additional ties are only possible when base scenario has tie breaks
        if (baseScenario.isTied()) {
          scenarios.add(baseScenario.append(Outcome.TIED_WINNER));
          // Cannot have a tie-breaker involving both a sore and non-sore loser
          if (baseScenario.hasTiedSoreLoser()) {
            scenarios.add(baseScenario.append(Outcome.TIED_SORE_LOSER));
          }
          else {
            // Difference between loser and early loser is order of elimination
            scenarios.add(baseScenario.append(Outcome.TIED_LOSER));
            scenarios.add(baseScenario.append(Outcome.TIED_EARLY_LOSER));
          }
        }
      }
    }
    return scenarios;
  }
}

