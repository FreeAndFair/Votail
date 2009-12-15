class BrokenDigitalDisplayClock extends DigitalDisplayClock {
  //@ requires time.length == 6;

  public BrokenDigitalDisplayClock( /*@ non_null @*/ int[] time) {
    this.time = time; // illegal!
  }

  public /*@ pure @*/ int[] expose() { return time; } // illegal!
}
