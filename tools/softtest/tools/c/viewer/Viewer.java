package softtest.tools.c.viewer;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import softtest.ast.c.CParser;
import softtest.pretreatment.PlatformType;
import softtest.pretreatment.Pretreatment;
import softtest.tools.c.jaxen.MatchesFunction;
import softtest.tools.c.viewer.gui.MainFrame;

/**
 * viewer's starter
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: Viewer.java,v 1.1 2010/01/05 01:48:54 qpeng Exp $
 */
public class Viewer
{
	private static String CONFIG_FILE = "config/config.ini";
	private final static String NOTE_PREFIX = "#";
	
	public static void main(String[] args)
	{
		Viewer v=new Viewer();
		String srcFileType=v.initFileType();
		System.out.println("Now the Parser is processing "+srcFileType+" type sourcefile.");
		MatchesFunction.registerSelfInSimpleContext();
		new MainFrame();
	}
	
	public String initFileType()
	{
		File configFile = new File(CONFIG_FILE);
		if (configFile.exists())
		{
			try
			{
				BufferedReader reader = new BufferedReader(new FileReader(
						configFile));
				String config;
				while ((config = reader.readLine()) != null)
				{
					if (config.trim().startsWith(NOTE_PREFIX) || config.trim().startsWith("-I")
							|| config.trim().startsWith("-D"))
					{
						continue;
					}
					if (config.trim().equalsIgnoreCase("-gcc"))
					{
						CParser.setType("gcc");
						return "gcc";
					} else if (config.trim().equalsIgnoreCase("-keil"))
					{
						CParser.setType("keil");
						return "keil";
					}
				}
			} catch (Exception e)
			{
				System.err.println("Error in reading the config file.");
				e.printStackTrace();
				return null;
			}
		}
		return null;
	}
}
