/**
 * @author Dermot Cochran, 2010, IT University of Copenhagen
 * 
 * This class generates ballot boxes that create an electoral scenario, 
 * for example, one winner by tie breaker and two losers, or one winner by 
 * quota, one winner as the highest continuing candidate on the last round, and
 * three losers below the threshold.
 */

package ie.votail.model.factory;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.ElectionConfiguration;
import ie.votail.model.Outcome;

import java.util.Map;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
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
  public static final String MODELS_VOTING_ALS = "./models/voting.als";
  protected final static Logger logger = Logger.getLogger(LOGGER_NAME);
  private static final int MAX_SCOPE = 50;
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
   * @return The ELection Configuration (null if generation fails)
   */
  public ElectionConfiguration /*@ non_null @*/ extractBallots(
    /*@ non_null*/ ElectoralScenario scenario, int scope) {
    
    final ElectionConfiguration electionConfiguration 
      = new ElectionConfiguration(scenario.canonical());
    electionConfiguration.setNumberOfWinners(scenario.numberOfWinners());
    final int numberOfSeats = scenario.numberOfWinners();
    if (scenario.isByeElection()) {
      electionConfiguration.setNumberOfSeats(1);
    }
    else {
      electionConfiguration.setNumberOfSeats(numberOfSeats);
    }
    final int numberOfCandidates = scenario.getNumberOfCandidates();
    electionConfiguration.setNumberOfCandidates(
      numberOfCandidates);
    logger.info(numberOfCandidates + " candidates for " + 
        numberOfSeats + " seats");
    
    // Find a ballot box which creates this scenario
    try {
      A4Solution solution = findSolution(scenario, scope);
      logger.info("Using scope = " + scope + " found scenario " + scenario);
      
      
      if (solution.satisfiable()) { // Extract ballots from the solution
      // Iterate through the solution and add each vote to the table
        for (Sig sig : solution.getAllReachableSigs()) {
          // Log the model version number
          if (sig.label.contains("Version")) {
            for (Field field : sig.getFields()) {
              if (field.label.contains("year")) {
                A4TupleSet tupleSet = solution.eval(field);
                logger.info(tupleSet.toString());
              }
              else if (field.label.contains("month")) {
                A4TupleSet tupleSet = solution.eval(field);
                logger.info(tupleSet.toString());
              }
              else if (field.label.contains("day")) {
                A4TupleSet tupleSet = solution.eval(field);
                logger.info(tupleSet.toString());
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
        logger.info("Scenario for " + scenario + " has " + 
          electionConfiguration);
        return electionConfiguration;
      } 
      // Increase the scope and try again
      if (!scenario.hasOutcome(Outcome.TiedSoreLoser) && scope < MAX_SCOPE) {
        return extractBallots (scenario, scope+1);
      }
      else {
        logger.info("Skipped this scenario " + scenario.toString());
        return electionConfiguration;
      }

    } catch (Err e) {
      // Log failure to find scenario
      logger.severe("Unable to find ballot box for this scenario "
                    + scenario.toString() + " with scope " + scope
                    + " and predicate " + scenario.toPredicate()
                    + " because " + e.msg);
      return electionConfiguration;
    }
  }

  /**
   * Find the Alloy solution for an electoral scenario
   * 
   * @param scenario
   * @param scope
   * @return
   * @throws Err
   * @throws ErrorSyntax
   */
  protected A4Solution findSolution(ElectoralScenario scenario, int scope) throws Err,
      ErrorSyntax {
    A4Reporter reporter = new A4Reporter();
    A4Options options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;
    Map<String, String> loaded = null;
    CompModule world = CompUtil.parseEverything_fromFile(reporter, loaded,
      modelName);
    SafeList<Pair<String, Expr>> facts = world.getAllFacts();
    Expr predicate = CompUtil.parseOneExpression_fromString(world,
      scenario.toPredicate());
    logger.finest("Using this predicate: " + predicate.toString() + " " + 
      predicate.getDescription());
    Command command = new Command(false, scope, DEFAULT_BIT_WIDTH, scope, 
      predicate);
    logger.info("using scope " + scope + " and bitwidth " + DEFAULT_BIT_WIDTH);
    A4Solution solution = TranslateAlloyToKodkod.execute_command(reporter,
      world.getAllReachableSigs(), command, options);
    logger.finest("Found this solution: " + solution.toString());
    return solution;
  }
}
