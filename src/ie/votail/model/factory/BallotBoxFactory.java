/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 * 
 * This class generates ballot boxes that fulfull a given scenario, by using
 * the Alloy Analayser API with a pre-defined model of PR-STV voting
 */

package ie.votail.model.factory;

import ie.votail.model.Scenario;
import ie.votail.model.Vote;
import ie.votail.model.VoteTable;

import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import election.tally.BallotBox;

/**
 * 
 */
public class BallotBoxFactory {

  private static final int DEFAULT_BIT_WIDTH = 4;
  protected Module world;
  private Logger logger;
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
  public BallotBoxFactory(String model_filename, String log_filename) {

    reporter = new A4Reporter();
    options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;
    logger = Logger.getLogger(log_filename);

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
   * @return The Ballot Box (empty if generation fails)
   */
  //@ requires scenario.numberOfWinners() < scope
  public /*@ non_null*/ BallotBox generateBallotBox(
    /*@ non_null*/ Scenario scenario, int scope) {

    Expr predicate;
    Command command;
    A4Solution solution;
    BallotBox ballotBox = null;

    // Find a ballot box which creates this scenario
    try {
      predicate = CompUtil.parseOneExpression_fromString(world,
        scenario.toPredicate());
      command = new Command(false, scope, DEFAULT_BIT_WIDTH, scope, predicate);
      solution = TranslateAlloyToKodkod.execute_command(reporter,
        world.getAllReachableSigs(), command, options);

      if (solution.satisfiable()) {
        ballotBox = extractBallotBox(solution);
        //@ assert ballotBox != null;
        logger.info("Scenario " + scenario.toString() + " has ballot box: "
                    + ballotBox.toString());
      } else {
        ballotBox = new BallotBox();
        logger.severe("No ballot box found with scope up to " + scope
                      + " for scenario " + scenario.toString());
      }

    } catch (Err e) {
      // Log failure to find scenario
      logger.severe("Unable to find ballot box for this scenario "
                    + scenario.toString() + " with scope " + scope
                    + " because " + e.msg);
    }
    return ballotBox;
  }

  /**
   * Extract ballots from the Alloy Analyser solution
   * 
   * @param solution
   *        The Alloy solution for a scenario
   * @return The Ballot Box
   */

  static public BallotBox extractBallotBox(A4Solution solution) throws Err {

    BallotBox ballotBox = new BallotBox();
    
    ie.votail.model.VoteTable voteTable = new VoteTable();
    
    Iterable<ExprVar> atoms = solution.getAllAtoms();

    // Iterate through the solution and add each ballot to the ballot box
    for (ExprVar atom : atoms) {

      // Extract ballots
      if (atom.label.contains("Vote")) {
        
        ie.votail.model.Vote vote = new Vote();
        
        voteTable.add(vote);
      }
    }
    return voteTable.makeBallotBox();
  }
}
