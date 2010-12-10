package ie.votail.model;

import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;

public class VoteTable {
  
  protected int numberOfBallots;
  protected ArrayList<Vote> votes;

  /**
   * 
   * @param solution
   */
  public VoteTable(A4Solution solution) {
    
    // Iterate through the solution and add each vote to the table
    for (Sig sig : solution.getAllReachableSigs()) {
      if (sig.label.contains("Vote")) {
        A4TupleSet tupleSet = solution.eval(sig);
        for (A4Tuple tuple : tupleSet) {
          // Tuple should consist of ballotID, candidateID and ranking
          this.add(new Vote(tuple));
        }
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
