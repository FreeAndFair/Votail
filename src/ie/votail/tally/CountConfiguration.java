package ie.votail.tally;

public class CountConfiguration {

  /**
   * Article 16 of the constitution of the Republic or Ireland specifies a
   * maximum of 30,000 people per seat, and the current electoral laws specify a
   * maximum of five seats per national constituency, so the maximum possible
   * number of ballots is 150,000.
   */
  public static final int MAXVOTES = ie.votail.tally.Ballot.MAX_BALLOTS;
  /**
   * Maximum possible number of counts
   * 
   * @design This value is not set by the legislation; it is chosen so that
   *         fixed length arrays can be used in the specification.
   */
  public static final int    MAXCOUNT = 50;
}