/*
 * Created on 17-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package election;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;
import java.util.StringTokenizer;

import javax.swing.JFrame;

/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class RetestPassFolder {

    static String retestFolderPath = "D:\\IESTestData\\Passes\\";
    static String retestFailsPath = "D:\\IESTestData\\Passes\\Fails\\";
    static boolean run = true;
    
    public static void testFolder(){
        JFrame frame = new JFrame();
        frame.addWindowListener(new WindowAdapter(){
			public void windowClosing(WindowEvent e)
			{
				if(run)
				    run =false;
				else
				    System.exit(0);
			}
		});
		frame.show();
        File retestFolder = new File(retestFolderPath);
        File[] subTestFolders = retestFolder.listFiles();
        
        StringBuffer failBuffer = new StringBuffer();
        int numPasses=0;
        int numFails=0;
        
        for (int i = 0; i < subTestFolders.length && run; i++){
            File subTestFolder = subTestFolders[i];
            File f = new File(retestFailsPath);
            if(subTestFolder.equals(f))
                continue;
            System.out.println("Testing: " + subTestFolder.getName());
            File[] folders = subTestFolder.listFiles();
            for (int j = 0; j < folders.length; j++) {
                File folder = folders[j];
	            StringTokenizer tokenizer = new StringTokenizer(folder.getName().toString()," - ");
	            tokenizer.nextToken();
	            String electionType = (String)tokenizer.nextToken();
	            String nSeats = (String)tokenizer.nextToken();
	            int numSeats = (new Integer(nSeats)).intValue();
	            int eType = -1;
	            if(electionType.equals("EU"))
	                eType = ElectionTypes.EUROPEAN_ELECTION;
	            else if(electionType.equals("LO"))
	                eType = ElectionTypes.LOCAL_ELECTION;
	            else if(electionType.equals("GE"))
	                eType = ElectionTypes.GENERAL_ELECTION;
	            ElectionReTester electionReTester =  new ElectionReTester();
	            boolean passed = electionReTester.testFolder(folder,numSeats,eType,false,false,null);
	            if(passed){
	                numPasses++;
	            } else {
	                numFails++;
	                failBuffer.append("Failed\t"+folder.getName()+"\t");
	                String copyFileName = retestFailsPath+folder.getName();
	                try {
                        FileUtils.copyDir(folder.getAbsolutePath(),copyFileName);
                    } catch (IOException e1) {
                        e1.printStackTrace();
                    }
	            } 
            }
        }        
        System.out.println(failBuffer);
        System.out.println("Num Passed\t"+numPasses);
        System.out.println("Num Fails\t"+numFails);
    }
    
    public static void main(String[] args) {
        RetestPassFolder.testFolder();
    }

}
