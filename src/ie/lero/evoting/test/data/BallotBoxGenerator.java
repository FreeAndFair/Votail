/**
 * Dermot Cochran, 2010, IT University of Copenhagen
 * 
 * This class generates ballot boxes that fulfull a given scenario, by using
 * the Alloy Analayser API with a pre-defined model of PR-STV voting
 */

package ie.lero.evoting.test.data;

import ie.votail.model.Scenario;

import java.util.Map;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import election.tally.BallotBox;

public class BallotBoxGenerator {

  private static final int MAX_SCOPE = 0;
  protected Logger logger;
  protected A4Reporter reporter;
  protected Map<String, String> loaded;
  protected A4Options options;
  protected Module world;
  
  /**
   * Start the generation of ballot boxes and load the Alloy model
   * 
   * @param model_filename The name of the Alloy model file
   * @param log_filename The name of the log file
   */
  BallotBoxGenerator(String model_filename, String  log_filename) {
    reporter = new A4Reporter();
    loaded = null;
    options = new A4Options();
    options.solver = A4Options.SatSolver.SAT4J;
    logger = Logger.getLogger(log_filename);
    
    try {
      world = CompUtil.parseEverything_fromFile(reporter, loaded, 
        model_filename);
    } catch (Err e) {
      world = null;
      logger.severe("Unable to find model " + model_filename 
        + "because of " + e.msg);
    }
  }
    
  /**
   * Generate a ballot box from a scenario description, using Alloy model
   * 
   * @param scenario The scenario which will be tested by this ballot box
   * @param scope The scope for model finding in Alloy Analyser
   * 
   * @return The Ballot Box (or null if generation fails)
   */
  /*@
   * require loaded != null;
   */
  public BallotBox generateBallotBox (/*@ non_null @*/ Scenario scenario, 
    int scope) {

    Expr predicate;
    Command command;
    A4Solution solution;
    BallotBox ballotBox = null;
    
    // Find a ballot box which fulfills this scenario
    try {
        predicate = CompUtil.parseOneExpression_fromString(world, 
          scenario.toPredicate());
        command = new Command(false,scope,scope/2,scope,predicate);
        solution = TranslateAlloyToKodkod.execute_command(reporter, 
          world.getAllReachableSigs(), command, options);
        
        if (solution.satisfiable()) {
          ballotBox = extractBallotBox (solution);
          logger.info("Scenario " + scenario.toString() + " has ballot box " 
            + ballotBox.toString());
        }
        else if (scope < MAX_SCOPE) {
          ballotBox = generateBallotBox(scenario,scope+1);
        }
        else {
          ballotBox = new BallotBox();
          logger.severe("No ballot box found with scope " + MAX_SCOPE 
            + "for scenario " + scenario.toString());
        }
        
      } catch (Err e) {
        // Log failure to find scenario
        logger.severe("Unable to find ballot box for this scenario " 
          + scenario.toString() + " with scope " + scope + " because of "
          + e.msg);
      }
      return ballotBox;
    }

  /**
   * Extract ballots from the Alloy Analyser solution
   * 
   * @param solution The Alloy solution for a scenario
   * @return The Ballot Box
   */
  
  public BallotBox extractBallotBox(A4Solution solution) {
    BallotBox ballotBox = new BallotBox();
    
    // Gte type signatures from the solution
    SafeList<Sig> sigs = solution.getAllReachableSigs();
    // Iterate through the solution and add each ballot to the ballot box
    for (Sig sig : sigs) {
      
      // Extract ballots
      if (sig.label.contains("Ballot")) {
        
        SafeList<Field> fields = sig.getFields();
        for (Field field : fields) {
          // Extract preferences
          if (field.label.equals("Preferences")) {
            int[] preferences = extractPreferences(field);
            // Add ballot to ballot box
            ballotBox.accept(preferences);
            
          }
        }
      }
    }
    
    return ballotBox;
  }

  /**
   * Extract list of preferences from an Alloy field API
   * 
   * @param field
   * @return
   */
  public int[] extractPreferences(Field field) {
    int numberOfPreferences = getNumberOfPreferences(field);
    int[] preferences = new int [numberOfPreferences];
    for (int i=0; i < numberOfPreferences; i++) {
      preferences[i] = getPreferences(field,i);
    }
     return null;
  }

  private int getPreferences(Field field, int i) {
    // TODO Auto-generated method stub
    return 0;
  }

  private int getNumberOfPreferences(Field field) {
    // TODO Auto-generated method stub
    return 0;
  }

    
}
