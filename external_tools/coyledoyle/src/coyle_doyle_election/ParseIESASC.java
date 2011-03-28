/*
 * Created on 28-Mar-2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coyle_doyle_election;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;
/**
 * @author doyledp
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class ParseIESASC
{
	private List votes;
	private String candidateNames[];
	
    public List parseFile(String filename){
        return parseFile(new File(filename));
    }
    
	public List parseFile(File filename)
	{
		BufferedReader in;
		try
		{
			votes = new ArrayList();
			in = new BufferedReader(new FileReader(filename));
			ArrayList names = new ArrayList();
			String line = in.readLine();
			StringTokenizer tokeniser = new StringTokenizer(line,"|");
			tokeniser.nextToken();
			while(tokeniser.hasMoreTokens())
			{
				String token = tokeniser.nextToken();
				names.add(token);
			}
			candidateNames = new String[names.size()];
			for (int i = 0; i < candidateNames.length; i++)
			{
				candidateNames[i] = (String)names.get(i);
			}
			int voteNumber =0;
			
			while(in.ready())
			{
				int[] prefs = new int[candidateNames.length];
				for (int j = 0; j < prefs.length; j++)
				{
					prefs[j] =0;	
				}
				line = in.readLine();
				tokeniser = new StringTokenizer(line,"|");
				int i = 0;
				while(tokeniser.hasMoreTokens())
				{
					String token = tokeniser.nextToken();
					if(i==0)
					{
						voteNumber = (new Integer(token)).intValue();
					}
					else
					{
						prefs[i-1] = (new Integer(token)).intValue();
					}
					i++;
				}
				BallotPaper bp = new BallotPaper(voteNumber,prefs);
				votes.add(bp);
			}
			in.close();
			return votes;
		}
		catch (FileNotFoundException e)
		{
			e.printStackTrace();
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return null;
	}
	
	public String[] getCandidateNames()
	{
		return candidateNames;
	}
}
