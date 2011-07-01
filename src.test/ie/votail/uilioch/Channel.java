package ie.votail.uilioch;

public interface Channel<T> {
  void put (T x) throws InterruptedException;
  T take () throws InterruptedException;
}
