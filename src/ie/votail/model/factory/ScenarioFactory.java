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
  /*@ requires 1 < numberOfOutcomes;
    @ ensures (numberOfOutcomes == 2) ==> (4 == \result.size());
    @ ensures (numberOfOutcomes == 3) ==> (26 == \result.size());
    @*/
  public /*@ pure */ ScenarioList find(int numberOfOutcomes, int numberOfSeats) {
    ScenarioList scenarios = new ScenarioList();
    if (numberOfOutcomes == 2) {
      
      // Winner gets majority of votes, loser reaches threshold
      Scenario commonScenario = new Scenario(numberOfSeats);
      commonScenario.addOutcome(Outcome.Winner);
      commonScenario.addOutcome(Outcome.Loser);
      scenarios.add(commonScenario);
      
      // Winner by tie breaker, loser reaches threshold
      Scenario tiedScenario = new Scenario(numberOfSeats);
      tiedScenario.addOutcome(Outcome.TiedWinner);
      tiedScenario.addOutcome(Outcome.TiedLoser);
      scenarios.add(tiedScenario);
      
      // Winner by tie breaker, loser below threshold
      Scenario landslideScenario = new Scenario(numberOfSeats);
      landslideScenario.addOutcome(Outcome.Winner);
      landslideScenario.addOutcome(Outcome.SoreLoser);
      scenarios.add(landslideScenario);
      
      // Winner by tie breaker, loser below threshold
      Scenario unusualScenario = new Scenario(numberOfSeats);
      unusualScenario.addOutcome(Outcome.TiedWinner);
      unusualScenario.addOutcome(Outcome.TiedSoreLoser);
      scenarios.add(unusualScenario);
    }
    else {
      // Extend the base scenario by adding one additional candidate outcome
      ScenarioList baseScenarios = find (numberOfOutcomes-1, numberOfSeats);
      Iterator<Scenario> iterator = baseScenarios.iterator();
      while (iterator.hasNext()) {
        Scenario baseScenario = iterator.next();
        scenarios.add(baseScenario.append(Outcome.Winner));
        scenarios.add(baseScenario.append(Outcome.QuotaWinner));
        scenarios.add(baseScenario.append(Outcome.CompromiseWinner));
        scenarios.add(baseScenario.append(Outcome.Loser));
        scenarios.add(baseScenario.append(Outcome.EarlyLoser));
        scenarios.add(baseScenario.append(Outcome.SoreLoser));
        // Additional ties are only possible when base scenario has tie breaks
        if (baseScenario.isTied()) {
          scenarios.add(baseScenario.append(Outcome.TiedWinner));
          // Cannot have a tie-breaker involving both a sore and non-sore loser
          if (baseScenario.hasTiedSoreLoser()) {
            scenarios.add(baseScenario.append(Outcome.TiedSoreLoser));
          }
          else {
            // Difference between loser and early loser is order of elimination
            scenarios.add(baseScenario.append(Outcome.TiedLoser));
            scenarios.add(baseScenario.append(Outcome.TiedEarlyLoser));
          }
        }
      }
    }
    return scenarios;
  }
}

