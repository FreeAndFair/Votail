package toolsForCoyleDoyle;

import java.util.logging.Logger;

public class Tools {
  
  /**
   * 
   */
  private Tools() {
    super();
  }

  static final Logger logger = Logger.getAnonymousLogger();
  
  public static int[] reverseList(final int[] tiedCandidates) {
    final int lengthOfList = tiedCandidates.length;
    int[] reversedList = new int[lengthOfList];
    for (int i = 0; i < lengthOfList; i++) {
      reversedList[i] = tiedCandidates[lengthOfList - i];
    }
    return reversedList;
  }
  
  public static void println(final String line) {
    logger.info(line);
  }
  
  public static void println(final int num) {
    logger.info(" " + num);
  }
  
}
