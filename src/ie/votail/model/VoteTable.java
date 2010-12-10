package ie.votail.model;

import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;

public class VoteTable {
  
  protected int numberOfBallots;
  protected ArrayList<Vote> votes;

  /**
   * 
   * @param solution
   */
  public VoteTable(A4Solution solution) {
    
    // Iterate through the solution and add each vote to the table
    for (ExprVar atom : solution.getAllAtoms()) {
      if (atom.label.contains("Vote")) {
        this.add(new Vote(atom));
      }
    }
  }

  /**
   * 
   * @param vote
   */
  public void add(/*@ non_null*/ Vote vote) {
    this.add(vote);
  }

}
