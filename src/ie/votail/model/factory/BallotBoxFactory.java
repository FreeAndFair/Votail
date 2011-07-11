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
import ie.votail.model.Outcome;

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
  
  public static final int DEFAULT_BIT_WIDTH = 7;
  public static final String LOGGER_NAME = "votail.log";
  public static final String MODELS_VOTING_ALS = "models/Voting.als";
  protected final static Logger logger = Logger.getLogger(LOGGER_NAME);
  protected static final int MAX_SCOPE = 15;
  protected String modelName;
  
  /**
   *
   */
  public BallotBoxFactory() {
    modelName = MODELS_VOTING_ALS;
    logger.info("Using model " + modelName);
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
  /*@ non_null*/ElectoralScenario scenario, int scope) {
    
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
  protected ElectionConfiguration extractBallots(/*@ non_null*/
  ElectoralScenario scenario, int scope, int upperBound) {
   
    
    // Find a ballot box which creates this scenario
    try {
      for (int i=scope; i < upperBound; i++) {
        A4Solution solution = findSolution(scenario, i);
        if (solution != null && solution.satisfiable()) {
          return parseSolution(scenario, scope, solution);
        }
      }
      
      logger.severe("Skipped this scenario " + scenario.toString());
      return null;
    }
    catch (Err e) {
      // Log failure to find scenario
      logger.severe("Unable to find ballot box for this scenario "
          + scenario.toString() + " with scope " + scope + " and predicate "
          + scenario.toPredicate() + " because " + e.toString());
      return null;
    }
  }

  /**
   * @param scenario
   * @param scope
   * @param electionConfiguration
   * @param solution
   */
  protected ElectionConfiguration parseSolution(ElectoralScenario scenario, int scope,
      A4Solution solution) {
    
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
        for (Field field : sig.getFields()) {
          if (field.label.contains("year")) {
            A4TupleSet tupleSet = solution.eval(field);
            logger.info("Model version year = " + tupleSet.toString());
          }
          else if (field.label.contains("month")) {
            A4TupleSet tupleSet = solution.eval(field);
            logger.info("Model version month = " + tupleSet.toString());
          }
          else if (field.label.contains("day")) {
            A4TupleSet tupleSet = solution.eval(field);
            logger.info("Model version day = " + tupleSet.toString());
          }
        }
      }
      
      else if (sig.label.contains("this/Ballot")) {
        for (Field field : sig.getFields()) {
          if (field.label.contains("preferences")) {
            A4TupleSet tupleSet = solution.eval(field);
            //@ assert tupleSet != null;
            electionConfiguration.extractPreferences(tupleSet);
          }
        }
      }
    }
    return electionConfiguration.trim();

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
  protected A4Solution findSolution(/*@ non_null @*/ ElectoralScenario scenario, 
      int scope) throws Err, ErrorSyntax {
    A4Reporter reporter = new A4Reporter();
    A4Options options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;
    Map<String, String> loaded = null;
    CompModule world;
    try {
      world = CompUtil.parseEverything_fromFile(reporter, loaded, modelName);
    }
    catch (Exception e) {
      logger.severe (e.toString());
      
      return null;
    }
    Expr predicate =
        CompUtil.parseOneExpression_fromString(world, scenario.toPredicate());
    logger.info("Trying scope " + scope + " for scenario " + scenario);
    Command command =
        new Command(false, scope, DEFAULT_BIT_WIDTH, scope, predicate);
    A4Solution solution =
        TranslateAlloyToKodkod.execute_command(reporter, world
            .getAllReachableSigs(), command, options);
    return solution;
  }
}
