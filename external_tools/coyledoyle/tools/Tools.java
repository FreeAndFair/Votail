package tools;

import java.util.logging.Logger;

public class Tools {
  
  static Logger logger = Logger.getAnonymousLogger();
  
  public static int[] reverseList(int[] tiedCandidates) {
    final int lengthOfList = tiedCandidates.length;
    int[] reversedList = new int[lengthOfList];
    for (int i = 0; i < lengthOfList; i++) {
      reversedList[i] = tiedCandidates[lengthOfList - i];
    }
    return reversedList;
  }
  
  public static void println(String line) {
    logger.info(line);
  }
  
  public static void println(int num) {
    logger.info(" " + num);
  }
  
}
