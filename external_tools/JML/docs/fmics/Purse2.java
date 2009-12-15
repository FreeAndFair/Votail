public class Purse2 {

    final int MAX_BALANCE;
    int balance;
    //@ invariant 0 <= balance && balance <= MAX_BALANCE;

    byte[] pin;
    /*@ invariant pin != null && pin.length == 4
      @           && (\forall int i; 0 <= i && i < 4;
      @                              0 <= pin[i] && pin[i] <= 9);
      @*/
       
    /*@ requires   amount >= 0;
      @ assignable balance;
      @ ensures    balance == \old(balance) - amount
      @            && \result == balance;
      @ signals (PurseException) balance == \old(balance);
      @*/
    int debit(int amount) throws PurseException {
        if (amount <= balance) { balance -= amount; return balance; }
        else { throw new PurseException("overdrawn by " + amount); }
    }
    
    /*@ requires   p != null && p.length >= 4;
      @ assignable \nothing;
      @ ensures    \result <==> (\forall int i; 0 <= i && i < 4;
      @                                         pin[i] == p[i]);
      @*/
    boolean checkPin(byte[] p) {
        boolean res = true;
        for (int i=0; i < 4; i++) { res = res && pin[i] == p[i]; }
        return res;
    }

    /*@ requires   0 < mb && 0 <= b && b <= mb
      @            && p != null && p.length == 4
      @            && (\forall int i; 0 <= i && i < 4;
      @                               0 <= p[i] && p[i] <= 9);
      @ assignable MAX_BALANCE, balance, pin;
      @ ensures    MAX_BALANCE == mb && balance == b
      @            && (\forall int i; 0 <= i && i < 4; p[i]==pin[i]);
      @*/
    Purse2(int mb, int b, byte[] p) {
        MAX_BALANCE = mb; balance = b; pin = (byte[])p.clone();
    }

    public String toString() {
        return "Purse(max=" + MAX_BALANCE + ", bal=" + balance
            + ", pin={" + pin[0] + pin[1] + pin[2] + pin[3] + "})";
    }
}
