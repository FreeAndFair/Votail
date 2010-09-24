package ie.lero.evoting.test.data;

import ie.votail.model.Scenario;

import java.io.IOException;
import java.util.Map;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import election.tally.BallotBox;

public class BallotBoxGenerator {
  private static final int MAX_SEQ = 10;

  // Import Alloy model of voting and ballot boxes
  
  private static final int SCOPE = 10;

  private static final int BITWIDTH = 6;

  protected Logger logger;
  
  private A4Reporter a4Reporter = new A4Reporter();
  private int numberOfCandidates;  
  // Generation of ballot boxes for each possible outcome
  private Map<String, String> loaded;

  private int scope,bitWidth,maxSequenceLength;
    
    public void loadModel(Map<String, String> loaded, String filename) throws Err {
      edu.mit.csail.sdg.alloy4compiler.parser.CompUtil.parseEverything_fromFile(a4Reporter, loaded, filename);
    }
    
    /**
     * Generate a ballot box from a scenario description, using Alloy model
     * 
     * @param scenario The scenario which will be tested by this ballot box
     * @return The Ballot Box (or null if generation fails)
     */
    public BallotBox generateBallotBox (/*@ non_null @*/ Scenario scenario) {

      Expr predicate = null;
      Module voting = null;
      try {
        predicate = CompUtil.parseOneExpression_fromString(voting, scenario.toPredicate());
        Command command = new Command(false,scope,bitWidth ,maxSequenceLength,predicate);
        
        CompModule model = CompUtil.parseEverything_fromFile(a4Reporter, loaded, "models/voting.als");
      } catch (Err e) {
        // Log failure to find scenario
        logger.severe("Failed to find ballot box for this scenario " + scenario.toString() + " because of "+ e.getLocalizedMessage());
      }
      
      // Extract ballot box from results
      BallotBox ballotBox = new BallotBox();
      
      // Run the predicate
      A4Solution solution = null;
      
      // Log the ballot box generation
      
      logger.info("Scenario " + scenario.toString() + " has ballot box " + ballotBox.toString());
      
      return ballotBox;
    }

    BallotBoxGenerator() {
      try {
        loadModel(null,"models/Voting.als");
        
      } catch (Err e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    /**
     * Ballot box format is:
     * 
     * <number of ballots>
     * <number of preferences> <preferences>
     * 
     * 
     * @param in
     * @return
     * @throws IOException
     */
    public BallotBox read(java.io.ObjectInputStream in) throws IOException {
          BallotBox box = new BallotBox();
          int numberOfBallots = in.readInt();
          for (int l=0; l<numberOfBallots; l++) {
            int numberOfPreferences = in.readInt();
            int[] preferences = new int[numberOfPreferences];
            for (int p=0; p<numberOfPreferences; p++) {
              preferences[p] = in.readInt();
            }
            box.accept(preferences);
          }
          return box;
      }

     public void write(java.io.ObjectOutputStream out, BallotBox box) throws IOException {
      }
    
     /**
      * Table of Outcomes:
      *   0 = Sore Loser
      *   
      *   9 = Winner
      *   
      *   #see Outcome class
      */
     
     // Generate the complete set of ballot box test data
     public static void Main() {
       
     }
}
