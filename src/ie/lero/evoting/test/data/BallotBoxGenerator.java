package ie.lero.evoting.test.data;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import election.tally.BallotBox;

public class BallotBoxGenerator {
  // Import Alloy model of voting and ballot boxes
  
    A4Reporter a4Reporter = new A4Reporter();  
  // Generation of ballot boxes for each possible outcome
    
    String prefix;
    String suffix;
    
    public void loadModel(Map<String, String> loaded, String filename) throws Err {
      edu.mit.csail.sdg.alloy4compiler.parser.CompUtil.parseEverything_fromFile(a4Reporter, loaded, filename);
    }
    
    public BallotBox getBallotBox (int n) throws IOException {
      // Read nth ballot box - resolve n into index of candidate outcomes (0 = sore loser, ..., 9 = winner);
      // If not found then generate all ballot boxes
      
      String filename = prefix + n + suffix;
      ObjectInputStream out = null;
      BallotBox ballotBox = null;
      try {
        ballotBox = read(out);
      } catch (ClassNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      
      return ballotBox;
    }

    public void createBallotBoxes() throws IOException {
      
      // For each candidate outcome, for up to five candidates
      
      // Load predicate for this scenario
      
      
      BallotBox ballotBox = new BallotBox();
      
      
      ObjectOutputStream file = null;
      // Save generated ballot box with the expected result in the first line
      write (file, ballotBox);
      return;
    }
    
    BallotBoxGenerator() {
      try {
        loadModel(null,"models/Voting.als");
        
      } catch (Err e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    public BallotBox read(java.io.ObjectInputStream in) throws IOException,
          ClassNotFoundException {
            return null;
      }

     public void write(java.io.ObjectOutputStream out, BallotBox box) throws IOException {
      }
    
     /**
      * Table of Outcomes:
      *   0 = Sore Loser
      *   
      *   9 = Winner
      */
}
