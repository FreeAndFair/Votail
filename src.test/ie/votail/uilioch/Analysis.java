package ie.votail.uilioch;

import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.logging.Logger;

import election.tally.Ballot;

public class Analysis {
  
  protected static final String ANALYSIS_FILENAME = "testdata/analysis.txt";
  protected static int counter = 1;
  
  public void add(ElectoralScenario scenario, ElectionData ballotBox) {
    Logger logger = Logger.getAnonymousLogger();
    
    try {
      
      FileOutputStream fos = new FileOutputStream(ANALYSIS_FILENAME, true);
      ObjectOutputStream out = new ObjectOutputStream(fos);
      
      out.writeChars("Scenario Number " + Integer.toString(counter++) + "\n");
      out.writeChars(scenario.toString() + "\n");
      // Number of Ballots
      out.writeChars("Number of ballots ");
      Ballot[] box = ballotBox.getBallots();
      final int numberOfBallots = box.length;
      out.writeChars(Integer.toString(numberOfBallots) + "\n");
      // Average Length of Ballots
      int sumOfLengths = 0;
      int maxLength = 1;
      for (int index = 0; index < numberOfBallots; index++) {
        final int lengthOfBallot = box[index].remainingPreferences();
        assert lengthOfBallot <= scenario.getNumberOfCandidates();
        sumOfLengths += lengthOfBallot;
        if (maxLength < lengthOfBallot) maxLength = lengthOfBallot;
      }
      out.writeChars("Average length of each ballot ");
      final int averageLength = 1 + (sumOfLengths / numberOfBallots);
      out.writeChars(Integer.toString(averageLength) + "\n");
      out.close();
      fos.close();
      
      logger.info("Wrote scenario number " + counter + " with "
          + numberOfBallots + " ballots of average length " + averageLength
          + " and maximum length of " + maxLength );
      
    }
    catch (FileNotFoundException e) {
      logger.info(e.toString());
    }
    catch (IOException e) {
      logger.info(e.toString());
    }
  }
  
}
