/**
 * @author Dermot Cochran, 2010-2011, IT University of Copenhagen
 * 
 *         This class generates ballot boxes that create an electoral scenario,
 *         for example, one winner by tie breaker and two losers, or one winner
 *         by
 *         quota, one winner as the highest continuing candidate on the last
 *         round, and
 *         three losers below the threshold.
 */

package ie.votail.model.factory;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;

import java.util.Map;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

/**
 * 
 */
public class BallotBoxFactory {
  
  public static final int BIT_WIDTH = 7;
  public static final String LOGGER_NAME = "votail.log";
  public static final String MODELS_VOTING_ALS = "models/Voting.als";
  protected final static Logger logger = Logger.getLogger(LOGGER_NAME);
  protected static final int MAX_SCOPE = 17;
  protected String modelName;

  protected ScenarioList impossibleScenarios;
  
  /**
   *
   */
  public BallotBoxFactory() {
    modelName = MODELS_VOTING_ALS;
    logger.info("Using model " + modelName);
    impossibleScenarios = new ScenarioList();
  }
  
  /**
   * Generate Ballots for an Election Configuration from an Electoral Scenario
   * 
   * @param scenario
   *          The scenario which will be tested by this ballot box
   * @param scope
   *          The scope for model finding in Alloy Analyser
   * @param byeElection
   * @return The Election Configuration (null if generation fails)
   */
  public ElectionConfiguration /*@ non_null @*/extractBallots(
    final /*@ non_null*/ ElectoralScenario scenario, final int scope) {
    
    return extractBallots(scenario, scope, MAX_SCOPE);
  }
  
  /**
   * Generate ballot box test data
   * 
   * @param scenario
   *          The set of election outcomes
   * @param scope
   *          The initial scope for the Alloy solution
   * @param upperBound
   *          The maximum scope
   * @return The Ballot Box
   */
  //@ requires 0 < scope && scope <= upperBound;
  public /*@ pure @*/ ElectionConfiguration extractBallots(/*@ non_null*/
      final ElectoralScenario scenario, final int scope, final int upperBound) {
    
    // Find a ballot box which creates this scenario
    for (int i=scope; i < upperBound; i++) {
      try {
        final A4Solution solution = findSolution(scenario, i);
        if (solution != null && solution.satisfiable()) {
          return parseSolution(scenario, scope, solution);
        }
      }
      catch (Err e) {
        // Log failure to find scenario
        logger.severe("Unable to find ballot box for this scenario "
          + scenario.toString() + " with scope " + scope + " and predicate "
          + scenario.toPredicate() + " because " + e.toString());
        return null;
      }
    }
      
    // No solution found implies that scenario might be impossible
    logger.info(
      "This scenario might be impossible " + 
      scenario.toString());
    impossibleScenarios.add(scenario);
    logger.info("Number of questionable scenarios so far: " + 
      impossibleScenarios.size());
    return null;
  }

  /**
   * @param scenario
   * @param scope
   * @param electionConfiguration
   * @param solution
   */
  protected ElectionConfiguration parseSolution(final ElectoralScenario scenario, 
      final int scope,
      final A4Solution solution) {
    
    final ElectionConfiguration electionConfiguration =
      new ElectionConfiguration(scenario.canonical());
  
    
    electionConfiguration.setNumberOfWinners(scenario.numberOfWinners());
    final int numberOfSeats = scenario.numberOfWinners();
    if (scenario.isByeElection()) {
      electionConfiguration.setNumberOfSeats(1);
    }
    else {
      electionConfiguration.setNumberOfSeats(numberOfSeats);
    }
    final int numberOfCandidates = scenario.getNumberOfCandidates();
    electionConfiguration.setNumberOfCandidates(numberOfCandidates);
    logger.info(numberOfCandidates + " candidates for " + numberOfSeats
        + " seats");

    logger.info("Using scope = " + scope + " found scenario " + scenario);
    
    // Iterate through the solution and add each vote to the table
    for (Sig sig : solution.getAllReachableSigs()) {
      // Log the model version number
      if (sig.label.contains("Version")) {
        logVersionNumber(solution, sig);
      }
      
      else if (sig.label.contains("this/Ballot")) {
        for (Field field : sig.getFields()) {
          if (field.label.contains("preferences")) {
            final A4TupleSet tupleSet = solution.eval(field);
            //@ assert tupleSet != null;
            electionConfiguration.extractPreferences(tupleSet);
          }
        }
      }
    }
    return electionConfiguration.trim();

  }

  /**
   * @param solution
   * @param sig
   */
  protected void logVersionNumber(final A4Solution solution, Sig sig) {
    for (Field field : sig.getFields()) {
      if (field.label.contains("year")) {
        final A4TupleSet tupleSet = solution.eval(field);
        logger.info("Model version year = " + tupleSet.toString());
      }
      else if (field.label.contains("month")) {
        final A4TupleSet tupleSet = solution.eval(field);
        logger.info("Model version month = " + tupleSet.toString());
      }
      else if (field.label.contains("day")) {
        final A4TupleSet tupleSet = solution.eval(field);
        logger.info("Model version day = " + tupleSet.toString());
      }
    }
  }
  
  /**
   * Find the Alloy solution for an electoral scenario
   * 
   * @param scenario
   *          The electoral scenario
   * @param scope
   *          The scope of the search
   * @return The Alloy solution
   * @throws Err
   * @throws ErrorSyntax
   */
  //@ requires 0 < scope;
  protected A4Solution findSolution(
      final /*@ non_null @*/ ElectoralScenario scenario, 
      final int scope) throws Err, ErrorSyntax {
    final A4Reporter reporter = new A4Reporter();
    final A4Options options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;
    final Map<String, String> loaded = null;
    CompModule world;
    try {
      world = CompUtil.parseEverything_fromFile(reporter, loaded, modelName);
    }
    catch (Exception e) {
      logger.severe (e.toString());
      
      return null;
    }
    final Expr predicate =
        CompUtil.parseOneExpression_fromString(world, scenario.toPredicate());
    logger.info("Trying scope " + scope + " for scenario " + scenario);
    final Command command =
        new Command(false, scope, BIT_WIDTH, scope, predicate);
    A4Solution solution =
        TranslateAlloyToKodkod.execute_command(reporter, world
            .getAllReachableSigs(), command, options);
    return solution;
  }
}
