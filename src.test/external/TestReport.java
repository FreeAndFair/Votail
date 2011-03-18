package external;

public class TestReport {

  protected String title;
  protected StringBuffer text;
  
  public TestReport() {
    text = new StringBuffer();
  }

  public void setTitle(String string) {
    this.title = string;
  }

  public void add(String string) {
    text.append(string);
  }
  
}
