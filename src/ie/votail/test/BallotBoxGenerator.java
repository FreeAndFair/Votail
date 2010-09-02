package ie.votail.test;

import ie.votail.tally.BallotBox;

import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;

public class BallotBoxGenerator {
  // Import Alloy model of voting and ballot boxes
  
    A4Reporter a4Reporter = new A4Reporter();  
  // Generation of ballot boxes for each possible outcome
    
    public void loadModel(Map<String, String> loaded, String filename) throws Err {
      edu.mit.csail.sdg.alloy4compiler.parser.CompUtil.parseEverything_fromFile(a4Reporter, loaded, filename);
    }
    
    public static BallotBox getBallotBox (int n) {
      // Load predicate for this scenario
      
      
      BallotBox ballotBox = new BallotBox();
      
      
      // Save generated ballot box
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
}
