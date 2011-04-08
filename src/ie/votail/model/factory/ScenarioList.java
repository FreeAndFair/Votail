/**
 * List of Electoral Scenarios.
 * 
 * @author Dermot Cochran, 2010-2011, IT University of Copenhagen, Denmark.
 */

package ie.votail.model.factory;

import ie.votail.model.ElectoralScenario;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInput;
import java.io.ObjectInputStream;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;

public class ScenarioList extends ArrayList<ElectoralScenario> implements Serializable {
  
  /**
   * 
   */
  private static final long serialVersionUID = 7207848959544184536L;

  // Maximum number of partitions within the list
  public static int MAX_PARTITIONS = 11; // Ten possible outcomes, plus one
  
  // Sublists of scenarios for each fixed number of winners
  protected ArrayList<ElectoralScenario>[] partitions;
  
  // Scenarios with a larger number of winners, not held in any partition
  protected ArrayList<ElectoralScenario> bucket;
  
  /**
   * Creates a new empty list of scenarios, with an empty bucket and
   * empty partitions.
   */
  /*@ ensures this.partitions.length == MAX_PARTITIONS;
    @ ensures this.bucket.size() == 0;
    @ ensures this.size() == 0;
    @*/
  @SuppressWarnings("unchecked")
  public ScenarioList() {
    this.partitions = new ArrayList[MAX_PARTITIONS];
    for (int i = 0; i < MAX_PARTITIONS; i++) {
      partitions[i] = new ArrayList<ElectoralScenario>();
    }
    bucket = new ArrayList<ElectoralScenario>();
  }
  
  /**
   * Replay scenario list from a stored file.
   * 
   * @param filename
   *          The name of the file
   * @throws IOException
   * @throws ClassNotFoundException
   */
  @SuppressWarnings("unchecked")
  public ScenarioList(String filename) throws IOException,
      ClassNotFoundException {
    InputStream file = new FileInputStream(filename);
    InputStream buffer = new BufferedInputStream(file);
    ObjectInput input = new ObjectInputStream(buffer);
    
    try {
      bucket = (ArrayList<ElectoralScenario>) input.readObject();
      partitions = (ArrayList<ElectoralScenario>[]) input.readObject();
    }
    finally {
      input.close();
      buffer.close();
      file.close();
    }
    
    // Recreate the full list from the bucket and partitions
    for (ElectoralScenario scenario : bucket) {
      super.add(scenario);
    }
    
    for (int i = 0; i < partitions.length; i++) {
      for (ElectoralScenario scenario : partitions[i]) {
        super.add(scenario);
      }
      
    }
  }
  
  /**
   * Discover whether a scenario is in the <code>ScenarioList</code>.
   * 
   * @param scenario
   *          The scenario to look for
   * @return <code>true</code> if the scenario is in the list
   */
  public boolean hasScenario(/*@ non_null @*/ ElectoralScenario scenario) {
    Iterator<ElectoralScenario> it = this.iterator();
    while (it.hasNext()) {
      if (it.next().equivalentTo(scenario)) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Add scenario to one of the partitions or to the bucket as well as adding
   * to the master list.
   * 
   * @param scenario
   *          The scenario to be added
   * @return <code>true</code> if this scenario is not already in list
   */
  /*@
   * ensures this.hasScenario(scenario);
   */
  @Override
  public boolean add(/*@ non_null*/ElectoralScenario scenario) {
    if (this.hasScenario(scenario)) {
      return false;
    }
    
    // Sort the scenario into canonical order before adding it
    ElectoralScenario canonical = scenario.canonical();
    
    // Also, add to sublist according to number of winners
    int partitionNumber = scenario.numberOfWinners();
    if (partitionNumber < MAX_PARTITIONS) {
      partitions[partitionNumber].add(canonical);
    }
    else {
      bucket.add(canonical);
    }
    return super.add(canonical);
  }
  
  /**
   * Get the number of scenarios with this exact number of winners, or the
   * number of scenarios in the bucket if there are more winners than
   * partitions
   * 
   * @param numberOfWinners
   *          The number of winners in each scenario
   * @return Either the number of scenarios in this partition or the bucket
   */
  /*@
   * requires 0 < numberOfWinners;
   * ensures 0 <= \result;
   */
  public/*@ pure*/int getNumberOfScenarios(int numberOfWinners) {
    if (numberOfWinners <= MAX_PARTITIONS) {
      return partitions[numberOfWinners].size();
    }
    return bucket.size();
  }
  
  /**
   * Store this scenario list in a file.
   * 
   * @param filename
   * @throws IOException
   */
  public void writeToFile(String filename) throws IOException {
    
    OutputStream file = new FileOutputStream(filename);
    OutputStream buffer = new BufferedOutputStream(file);
    ObjectOutput output = new ObjectOutputStream(buffer);
    try {
      output.writeObject(bucket);
      output.writeObject(partitions);
    }
    finally {
      output.close();
      buffer.close();
      file.close();
    }
  }
}
