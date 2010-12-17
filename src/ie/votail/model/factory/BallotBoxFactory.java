/**
 * @author Dermot Cochran, 2010, IT University of Copenhagen
 * 
 * This class generates ballot boxes that create an electoral scenario, 
 * for example, one winner by tie breaker and two losers, or one winner by 
 * quota, one winner as the highest continuing candidate on the last round, and
 * three losers below the threshold.
 */

package ie.votail.model.factory;

import ie.votail.model.Scenario;
import ie.votail.model.Vote;
import ie.votail.model.VoteTable;

import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import election.tally.BallotBox;

/**
 * 
 */
public class BallotBoxFactory {

  private static final int DEFAULT_BIT_WIDTH = 6;
  private static final String LOG_FILENAME = "testdata/generation.log";
  protected Module world;
  
  /**
   * 
   */
  private final static Logger logger = Logger.getLogger(LOG_FILENAME);
  protected A4Reporter reporter;
  protected A4Options options;

  /**
   * Start the generation of ballot boxes and load the Alloy model
   * 
   * @param model_filename
   *        The name of the Alloy model file
   * @param log_filename
   *        The name of the log file
   */
  public BallotBoxFactory(String model_filename) {

    reporter = new A4Reporter();
    options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;

    try {
      world = CompUtil.parseEverything_fromFile(reporter, null,
        model_filename);
    } catch (Err e) {
      world = null;
      logger.severe("Unable to find model " + model_filename + " because of "
                    + e.msg);
    }
  }

  /**
   * Generate a ballot box from a scenario description, using Alloy model
   * 
   * @param scenario The scenario which will be tested by this ballot box
   * @param scope The scope for model finding in Alloy Analyser
   * @return The Ballot Box (null if generation fails)
   */
  public BallotBox generateBallotBox(
    /*@ non_null*/ Scenario scenario, int scope) {
    
    // Find a ballot box which creates this scenario
    try {
      A4Solution solution = findSolution(scenario, scope);
      final VoteTable voteTable = new VoteTable();
      
      if (solution.satisfiable()) { // Extract ballots from the solution
     // Iterate through the solution and add each vote to the table
        for (Sig sig : solution.getAllReachableSigs()) {
          if (sig.label.contains("this/Vote")) {
            
            for (Field field : sig.getFields()) {
              
              A4TupleSet tupleSet = solution.eval(field);
              //@ assert tupleSet != null;
              
              if (field.label.contains("ballot")) {
                voteTable.extractBallotIDs(tupleSet);
              }
              else if (field.label.contains("ranking")) {
                voteTable.extractRankings(tupleSet);
              }
              else if (field.label.contains("candidate")) {
                voteTable.extractCandidateIDs(tupleSet);
              }
              else {
                logger.warning("Unexpected field called " + field.label + 
                  " in signature of " + sig.label);
              }
            }
          }
        }
        BallotBox ballotBox = voteTable.getBallotBox();
        logger.info("Scenario " + scenario.toString() + " has ballot box: "
              + ballotBox.toString());
        return ballotBox;
      } 
      // Increase the scope and try again
      return generateBallotBox (scenario, scope+1);

    } catch (Err e) {
      // Log failure to find scenario
      logger.severe("Unable to find ballot box for this scenario "
                    + scenario.toString() + " with scope " + scope
                    + " because " + e.msg);
      return null;
    }
  }

  /**
   * @param scenario
   * @param scope
   * @return
   * @throws Err
   * @throws ErrorSyntax
   */
  protected A4Solution findSolution(Scenario scenario, int scope) throws Err,
      ErrorSyntax {
    Expr predicate = CompUtil.parseOneExpression_fromString(world,
      scenario.toPredicate());
    Command command = new Command(false, scope, DEFAULT_BIT_WIDTH, scope, 
                                  predicate);
    A4Solution solution = TranslateAlloyToKodkod.execute_command(reporter,
      world.getAllReachableSigs(), command, options);
    return solution;
  }
}
