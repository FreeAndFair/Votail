package ie.lero.evoting.test.data;

import ie.votail.model.Scenario;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Map;

import com.sun.org.apache.bcel.internal.classfile.InnerClass;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import election.tally.Ballot;
import election.tally.BallotBox;

public class BallotBoxGenerator {
  // Import Alloy model of voting and ballot boxes
  
    A4Reporter a4Reporter = new A4Reporter();  
  // Generation of ballot boxes for each possible outcome
    
    public void loadModel(Map<String, String> loaded, String filename) throws Err {
      edu.mit.csail.sdg.alloy4compiler.parser.CompUtil.parseEverything_fromFile(a4Reporter, loaded, filename);
    }
    
    public BallotBox generateBallotBox (Scenario scenario) throws IOException {
      // Read nth ballot box - resolve n into index of candidate outcomes (0 = sore loser, ..., 9 = winner);
      // If not found then generate all ballot boxes
      
      // Create Alloy Scenario as a Predicate
      
      // Load Alloy Model
      
      // Extract ballot box from results
      BallotBox ballotBox = null;

      
      // Log the ballot box generation
      
      log (scenario, ballotBox);
      
      return ballotBox;
    }

    
    private void log(Scenario scenario, BallotBox ballotBox) {
      // TODO Auto-generated method stub
      
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
