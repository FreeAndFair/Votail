package election.tally;

/**
 * @author Dermot Cochran
 * @copyright Systems Research Group and University College Dublin, Ireland.
 * @reviewer Joe Kiniry
 */ 

/** Data transfer structure for set of all valid votes */
public class BallotBox {
	  
  /** List of valid ballot papers */
  // @review kiniry 1 Mar 2006 - This first invariant can be captured
  // using the JML keyword \nonnullelements.  I have changed the type
  // annotation below on the ballots field to reflect such.
  //@ public invariant \nonnullelements (ballots);

  // @review kiniry 1 Mar 2006 - I would express each invariant that
  // is approximately this complex in English as well as in JML.
  // E.g., it is not clear to me that this invariant is capturing what
  // you really meant to say because I do not know what high-level
  // constraints are being expressed.  For this particular invariant,
  // is the constraint no two ballot IDs in a ballot box are the same?
  // If so, I would express this invariant differently in a manner
  // that is more mathematically clean but perhaps less "efficient"
  // when viewing the expression from a computational viewpoint.
  /**
   * @constraint No two ballot IDs in a ballot box are the same.
   */
  /*@ public invariant (\forall int i, j;
    @                   0 <= i & i < numberOfBallots &
    @                   0 <= j & j < numberOfBallots &
    @                   i != j;
    @                   ballots[i].ballotID != ballots[j].ballotID);
    @*/
  public /*@ non_null @*/ Ballot[] ballots;
    
  // @review kiniry 1 Mar 2006 - There were missing '@' signs here, so
  // these specs were not being interpreted.
  
  // @review kiniry 1 Mar 2006 - You made a design decision in
  // choosing an long for the numberOfBallots property of a ballot box.
  // How do you justify that decision?  Is it based upon law, the
  // current population of Ireland, etc.?  If there is no concrete
  // restriction or assumption, is it not safer to make this
  // representation a long at no appreciable loss of complexity?
  // Obviously the type signature of the aforementioned size() method
  // would change as well.

  // @review kiniry 1 Mar 2006 - Abstraction is lacking for this type
  // interface.  In particular, I would introduce a size method:
  /**
   * @return the number of ballots in this ballot box.
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ long size();

  // ...and therefore change the visibility of numberOfBallots to private
  // and abstract these invariants to use the pure method.

  //@ public invariant 0 <= numberOfBallots;
  //@ public initially numberOfBallots == 0;
  //@ public constraint numberOfBallots >= \old (numberOfBallots);
  public int numberOfBallots;
    
  // @review kiniry 1 Mar 2006 - This postcondition is redundant given
  // your initially assertion above.

  /*@ public normal_behavior
    @   ensures numberOfBallots == 0;
    @*/
  public /*@ pure @*/ BallotBox();
}