package ie.votail.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

public class Logger {
  
  File file;
  FileOutputStream stream;
  
  /**
   * Open a new log file
   */
  public Logger (String filename) {
    try {
      stream = new FileOutputStream (filename + System.currentTimeMillis(), true);
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  /** 
   * Write another line to the log file
   * 
   */
  public void add (String line) {
     try {
      stream.write(line.getBytes());
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
}
