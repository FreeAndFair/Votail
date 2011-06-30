package ie.votail.uilioch;

public interface Channel {
  void put (Object x) throws InterruptedException;
  Object take () throws InterruptedException;
}
