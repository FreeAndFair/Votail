/*
 * Created on 10-Oct-2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle_election;

import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.nio.channels.FileChannel;

/**
 * @author Administrator
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class FileUtils {

	public static boolean moveDir(String sourcePath, String destPath) throws IOException
	{
		boolean result;
		result = copyDir(sourcePath,destPath,true);
		if(result)
		{
			File folder = new File(sourcePath);
            result = folder.delete();
		}
		return result;
	}
	
	public static boolean copyDir(String sourcePath, String destPath) throws IOException
	{
		boolean result;
		result = copyDir(sourcePath,destPath,false);
		return result;
	}
	
	private static boolean copyDir(String sourcePath, String destPath, boolean delete) throws IOException
	{
		File sourceDir = new File(sourcePath);
		if(!sourceDir.isDirectory())
			return false;
		
		File destDir = new File(destPath);
		if(!destDir.exists())
			destDir.mkdirs();
	   
		File[] children = sourceDir.listFiles();
		if (children == null) {
			System.out.println("In children = null");
			// Either dir does not exist or is not a directory
		} 
		else
		{
			for (int i=0; i<children.length; i++) 
			{
				// Get filename of file or directory
				if(children[i].isDirectory())
				{
					copyDir(children[i].getPath(),destPath+"/"+children[i].getName(),delete);
					File f = new File(children[i].getPath());
					f.delete();
				}
				else
				{
					String filename = children[i].getName();
					FileChannel srcChannel = new FileInputStream(children[i].getPath()).getChannel();
					FileChannel dstChannel = new FileOutputStream(destPath +"/"+ filename).getChannel();            
					// Copy file contents from source to destination        
					dstChannel.transferFrom(srcChannel, 0, srcChannel.size());            
					// Close the channels        
					srcChannel.close();        
					dstChannel.close();
					
					if(delete)
					{
						try
						{
							File f = new File(children[i].getPath());
							f.delete();
						}catch(Exception e)
						{
							e.printStackTrace();
						}
					}
				}
			}
		}
		return true;
	}

    /**
     * Outputs the contents of the buffer to the file f
     * @param f - the file to export to 
     * @param buffer - the contents to export
     * @return
     */
    public static boolean outputFile(File f,String buffer){
        boolean result = false;
        byte[] data;
        data = buffer.toString().getBytes();
        try
        {
            f.createNewFile();
            FileOutputStream out = new FileOutputStream(f);
            DataOutputStream dataOut = new DataOutputStream(out);           
            dataOut.write(data, 0 , data.length);
            out.close();
            result=true;
        }
        catch(FileNotFoundException e)
        {
            e.printStackTrace();
        }
        catch(IOException e)
        {
            e.printStackTrace();
        }

        return result;       
    }
    
    public static String readFile(File f){
        String s = null;
        
        try {
            BufferedReader br = new BufferedReader(new FileReader(f));
            StringBuffer buffer = new StringBuffer();
            while(br.ready()){
                buffer.append(br.readLine());
            }
            s = buffer.toString();
        } catch (FileNotFoundException e) {    
            System.out.println(f.getAbsolutePath());
            e.printStackTrace();    
        } catch (IOException e) {
            e.printStackTrace();    
        }
        return s;
    }
}
