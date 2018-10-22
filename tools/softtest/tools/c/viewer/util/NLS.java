package softtest.tools.c.viewer.util;

import java.util.ResourceBundle;

/**
 * helps with internationalization
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: NLS.java,v 1.1 2010/01/05 01:48:54 qpeng Exp $
 */
public class NLS
{
	private final static ResourceBundle bundle;

	static
	{
		bundle = ResourceBundle.getBundle("softtest.tools.c.viewer.resources.viewer_strings");
	}

	/**
	 * translates the given key to the message
	 * 
	 * @param key
	 *            key to be translated
	 * @return translated string
	 */
	public static String nls(String key)
	{
		return bundle.getString(key);
	}
}
