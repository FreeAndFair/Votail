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
  
  protected static final String WHITE_SPACE = " ";
  protected static final String ANALYSIS_FILENAME = "testdata/analysis.txt";
  protected static int counter = 1;
  
  public final void add(final ElectoralScenario scenario, 
      final ElectionData ballotBox) {
    final Logger logger = Logger.getAnonymousLogger();
    
    try {
      
      final FileOutputStream fos = new FileOutputStream(ANALYSIS_FILENAME);
      final ObjectOutputStream out = new ObjectOutputStream(fos);
      
      out.writeChars("Scenario Number " + Integer.toString(counter++) + 
          Analysis.WHITE_SPACE);
      out.writeChars(scenario.toString() + Analysis.WHITE_SPACE);

      out.writeChars("Number of ballots ");
      final Ballot[] box = ballotBox.getBallots();
      final int numberOfBallots = box.length;
      out.writeChars(Integer.toString(numberOfBallots) + Analysis.WHITE_SPACE);

      int sumOfLengths = 0;
      int maxLength = 1;
      for (int index = 0; index < numberOfBallots; index++) {
        final int lengthOfBallot = box[index].remainingPreferences();

        sumOfLengths += lengthOfBallot;
        if (maxLength < lengthOfBallot) {
          maxLength = lengthOfBallot;
        }
      }
      out.writeChars("Average length of each ballot ");
      final int averageLength = 1 + (sumOfLengths / numberOfBallots);
      out.writeChars(Integer.toString(averageLength) + Analysis.WHITE_SPACE);
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
