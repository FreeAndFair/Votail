package ie.votail.uilioch;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.logging.Logger;

import election.tally.Ballot;

import ie.votail.model.ElectionConfiguration;
import ie.votail.model.ElectoralScenario;
import ie.votail.model.data.ElectionData;

public class Analysis {

  protected static final String ANALYSIS_FILENAME = "testdata/analysis.txt";

  public void add(ElectoralScenario scenario, ElectionConfiguration ballots) {
    Logger logger = Logger.getAnonymousLogger();

  
    try {
    
      FileOutputStream fos = new FileOutputStream(ANALYSIS_FILENAME, true);
      ObjectOutputStream out = new ObjectOutputStream(fos);
      
      out.writeChars(scenario.toString());
      // Number of Ballots
      out.writeChars("Number of ballots ");
      final int numberOfBallots = ballots.getBallots().length;
      out.writeInt(numberOfBallots);
      // Average Length of Ballots
      int sumOfLengths = 0;
      Ballot[] box = ballots.getBallots();
      for (int index = 0; index < numberOfBallots; index++) {
        sumOfLengths += box[index].remainingPreferences();
      }
      out.writeChars("Average length of each ballot ");
      final int averageLength = 1+(sumOfLengths/numberOfBallots);
      out.writeInt(averageLength);
      out.close();
      fos.close();
    
  }
    catch (FileNotFoundException e) {
      logger.info(e.toString());
    }
    catch (IOException e) {
      logger.info(e.toString());
    }
  }
  
}
