/**
 * Find all PR-STV scenarios that match a fixed number of candidate outcomes.
 * 
 * @author Dermot Cochran, 2010-2011, IT University of Copenhagen
 */

package ie.votail.model.factory;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.Method;
import ie.votail.model.Outcome;

import java.util.Iterator;

public class ScenarioFactory {
  
  /**
   * Find all election scenarios for a given number of outcomes
   * 
   * @param numberOfOutcomes
   *          The number of candidate outcomes
   * @return All election scenarios with this number of outcomes
   */
  public/*@ pure @*/ScenarioList find(final int numberOfOutcomes, 
      final int numberOfSeats,
      final Method method) {
    final ScenarioList scenarios = new ScenarioList();
    if (numberOfOutcomes == 2) {
      findBaseScenarios(method, scenarios, false); // full election
      findBaseScenarios(method, scenarios, true); // special election
    }
    else {
      // Extend the base scenario by adding one additional candidate outcome
      final ScenarioList baseScenarios =
          find(numberOfOutcomes - 1, numberOfSeats, method);
      final Iterator<ElectoralScenario> iterator = baseScenarios.iterator();
      while (iterator.hasNext()) {
        final ElectoralScenario baseScenario = iterator.next();
        scenarios.add(baseScenario.append(Outcome.Winner));
        if (!baseScenario.hasOutcome(Outcome.TiedSoreLoser)) {
          // Cannot have a Loser with a Tied Sore Loser or Tied Early Loser
          scenarios.add(baseScenario.append(Outcome.Loser));
        }
        scenarios.add(baseScenario.append(Outcome.SoreLoser));
        if (method == Method.STV) {
          scenarios.add(baseScenario.append(Outcome.SurplusWinner));
          scenarios.add(baseScenario.append(Outcome.QuotaWinner));
          scenarios.add(baseScenario.append(Outcome.WinnerNonTransferable));
          scenarios
              .add(baseScenario.append(Outcome.QuotaWinnerNonTransferable));
          scenarios.add(baseScenario.append(Outcome.AboveQuotaWinner));
          scenarios.add(baseScenario.append(Outcome.CompromiseWinner));
          scenarios.add(baseScenario.append(Outcome.EarlySoreLoser));
          scenarios.add(baseScenario
              .append(Outcome.EarlySoreLoserNonTransferable));
          if (!baseScenario.hasOutcome(Outcome.TiedSoreLoser)) {
            // Cannot have an Early Loser with a Tied Sore Loser
            scenarios.add(baseScenario.append(Outcome.EarlyLoser));
            scenarios.add(baseScenario
                .append(Outcome.EarlyLoserNonTransferable));
          }
        }
        // Additional ties are only possible when base scenario has tie breaks
        if (baseScenario.isTied()) {
          scenarios.add(baseScenario.append(Outcome.TiedWinner));
          // Cannot have a tie-breaker involving both a sore and non-sore loser
          if (baseScenario.hasOutcome(Outcome.TiedSoreLoser)) {
            scenarios.add(baseScenario.append(Outcome.TiedSoreLoser));
          }
          else {
            if (!baseScenario.hasOutcome(Outcome.TiedSoreLoser)) {
              // Cannot have a Tied Loser with a Tied Sore Loser
              scenarios.add(baseScenario.append(Outcome.TiedLoser));
              
            }
          }
        }
      }
    }
    return scenarios;
  }
  
  /**
   * @param method
   * @param scenarios
   * @param byeElection
   */
  protected void findBaseScenarios(final Method method, 
      final ScenarioList scenarios,
      boolean byeElection) {
    // Winner gets majority of votes, loser reaches threshold
    final ElectoralScenario commonScenario =
        new ElectoralScenario(method, byeElection);
    commonScenario.addOutcome(Outcome.Winner);
    commonScenario.addOutcome(Outcome.Loser);
    scenarios.add(commonScenario);
    
    // Winner by tie breaker, loser reaches threshold
    final ElectoralScenario tiedScenario = new ElectoralScenario(method, byeElection);
    tiedScenario.addOutcome(Outcome.TiedWinner);
    tiedScenario.addOutcome(Outcome.TiedLoser);
    scenarios.add(tiedScenario);
    
    // Winner by tie breaker, loser below threshold
    ElectoralScenario landslideScenario =
        new ElectoralScenario(method, byeElection);
    landslideScenario.addOutcome(Outcome.Winner);
    landslideScenario.addOutcome(Outcome.SoreLoser);
    scenarios.add(landslideScenario);
    
    // Winner by tie breaker, loser below threshold
    if (method == Method.STV) {
      ElectoralScenario unusualScenario =
          new ElectoralScenario(method, byeElection);
      unusualScenario.addOutcome(Outcome.TiedWinner);
      unusualScenario.addOutcome(Outcome.TiedSoreLoser);
      scenarios.add(unusualScenario);
    }
  }
}
