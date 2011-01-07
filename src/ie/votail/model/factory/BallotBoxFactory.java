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

  public static final int DEFAULT_BIT_WIDTH = 6;
  public static final String LOG_FILENAME = "VoteFactory.log";
  public static final String MODELS_VOTING_ALS = "models/voting.als";
  protected final static Logger logger = Logger.getLogger(LOG_FILENAME);
  protected String modelName;

  /**
   *
   */
  public BallotBoxFactory() {
    modelName = MODELS_VOTING_ALS;
  }

  /**
   * Generate a ballot box from a scenario description, using Alloy model
   * 
   * @param scenario The scenario which will be tested by this ballot box
   * @param scope The scope for model finding in Alloy Analyser
   * @return The Ballot Box (null if generation fails)
   */
  public ElectionConfiguration extractBallots(
    /*@ non_null*/ ElectoralScenario scenario, int scope) {
    
    final ElectionConfiguration electionConfiguration = new ElectionConfiguration(LOG_FILENAME);
    electionConfiguration.setNumberOfWinners(scenario.numberOfWinners());
    electionConfiguration.setNumberOfSeats(scenario.getNumberOfSeats());
    electionConfiguration.setNumberOfCandidates(scenario.getNumberOfCandidates());
    
    // Find a ballot box which creates this scenario
    try {
      A4Solution solution = findSolution(scenario, scope);
      
      if (solution.satisfiable()) { // Extract ballots from the solution
      // Iterate through the solution and add each vote to the table
        for (Sig sig : solution.getAllReachableSigs()) {
          // Log the model version number
          if (sig.label.contains("version")) {
            logger.info(sig.getDescription());
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
      return extractBallots (scenario, scope+1);

    } catch (Err e) {
      // Log failure to find scenario
      logger.severe("Unable to find ballot box for this scenario "
                    + scenario.toString() + " with scope " + scope
                    + " because " + e.msg);
      return null;
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
    CompModule world = CompUtil.parseEverything_fromFile(reporter, null,
      modelName);
    Expr predicate = CompUtil.parseOneExpression_fromString(world,
      scenario.toPredicate());
    Command command = new Command(false, scope, DEFAULT_BIT_WIDTH, scope, 
                                  predicate);
    A4Solution solution = TranslateAlloyToKodkod.execute_command(reporter,
      world.getAllReachableSigs(), command, options);
    return solution;
  }
}
