package ie.lero.evoting.test.data;

import ie.votail.model.Outcome;
import ie.votail.model.Scenario;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.logging.Logger;

public class ScenarioGenerator {

  public static final String SCENARIOS_LOG = "scenarios.log";
  Logger scenarioLogger;
  
  public ScenarioGenerator() {
    scenarioLogger = Logger.getLogger(ScenarioGenerator.SCENARIOS_LOG);
  }

  /**
   * Find all election scenarios
   * 
   * @param numberOfOutcomes
   * @return
   */
  /*@
   * require 1 < numberOfOuctomes;
   */
  public ArrayList<Scenario> find(int numberOfOutcomes) {
    ArrayList<Scenario> scenarios = new ArrayList<Scenario>();
    if (numberOfOutcomes == 2) {
      
      // Winner gets majority of votes, losers reaches threshold
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
      // Extend the base scenario for one less outcome
      ArrayList<Scenario> baseScenarios = find (numberOfOutcomes-1);
      Iterator<Scenario> iterator = baseScenarios.iterator();
      while (iterator.hasNext()) {
        Scenario baseScenario = iterator.next();
        scenarios.add(baseScenario.append(Outcome.WINNER));
        scenarios.add(baseScenario.append(Outcome.QUOTA_WINNER));
        scenarios.add(baseScenario.append(Outcome.COMPROMISE_WINNER));
        scenarios.add(baseScenario.append(Outcome.LOSER));
        scenarios.add(baseScenario.append(Outcome.EARLY_LOSER));
        scenarios.add(baseScenario.append(Outcome.SORE_LOSER));
        // Additional ties are only possible when base scenario has ties
        if (baseScenario.isTied()) {
          scenarios.add(baseScenario.append(Outcome.TIED_WINNER));
          scenarios.add(baseScenario.append(Outcome.TIED_LOSER));
          scenarios.add(baseScenario.append(Outcome.TIED_EARLY_LOSER));
          scenarios.add(baseScenario.append(Outcome.TIED_WINNER));
        }
      }
    }
    return unique(scenarios);
  }

  /**
   * Apply canonical sorting and remove duplicate scenarios
   * @param scenarios
   * @return Distinct scenarios
   */
  private ArrayList<Scenario> unique(ArrayList<Scenario> scenarios) {
    ArrayList<Scenario> distinctScenarios = new ArrayList<Scenario>();
    Iterator<Scenario> iterator = scenarios.iterator();
    while (iterator.hasNext()) {
      Scenario scenario = iterator.next().canonical();
      if (!distinctScenarios.contains(scenario)) {
        distinctScenarios.add(scenario);
      }
    }
    return distinctScenarios;
  }
  
  public void generate (int numberOfOutcomes) {
    // TODO
  }
  
  public Scenario getScenario (int index) {
    return null; // TODO
  }
}

