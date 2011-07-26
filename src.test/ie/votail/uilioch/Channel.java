package ie.votail.uilioch;

public interface Channel<T> {
  void put (T task) throws InterruptedException;
  T take () throws InterruptedException;
}
