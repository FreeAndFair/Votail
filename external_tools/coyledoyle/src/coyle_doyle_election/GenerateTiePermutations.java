/*
 * Created on 27-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle_election;

import java.io.File;
import java.util.Arrays;
import java.util.StringTokenizer;

public class GenerateTiePermutations {
    
    //private static final String TIES_FOLDER = "d:\\IES-Testdata\\TestingTies\\";
    private static final String TIES_FOLDER = "d:\\IES-Testdata\\Ties\\";
    
    int numofElections = 0;
    int numFolders=0;

    //folder is the folder containing folders of sub folders for checking
    public GenerateTiePermutations(File folder){
        File[] subFolders = folder.listFiles();
        Arrays.sort(subFolders);
        for (int i = 0; i < subFolders.length; i++) {
//            if (!subFolders[i].getName().equals("T2F")) {
//                continue;
//            }
            File[] testFolders = subFolders[i].listFiles();
            for (int j = 0; j < testFolders.length; j++) {
                
                TieIterator iterator = null;
                try {
                    File testFolder = testFolders[j];
                    iterator = new TieIterator();
                    iterator.testFolder(testFolder);
                    StringTokenizer tokenizer = new StringTokenizer(testFolder.getName()," - ");
                    tokenizer.nextToken();
                    String header = tokenizer.nextToken();
                    header = header + " - " + tokenizer.nextToken();
                    header = header + " - " + tokenizer.nextToken();
                    header = header + " - " + tokenizer.nextToken();
                    header = header + " - " + tokenizer.nextToken();
                    FileUtils.outputFile(new File(testFolder.getAbsolutePath()+"\\ties.txt"),header+"\n"+iterator.getOrders());
                } catch (RuntimeException e) {
                    System.out.println("Folder: " + testFolders[j]);
                    e.printStackTrace();
                }
                numFolders++;
                numofElections+=iterator.getNumElections();
                if(numFolders%100==0){
                    System.out.println(numFolders + " elections checked with " + numofElections + " permutations");
                }
            }
        }
    }
    
    /**
     * @param args
     */
    public static void main(String[] args) {
        new GenerateTiePermutations(new File(TIES_FOLDER));
    }

}
