package softtest.tools.c.viewer.gui.menu;

import softtest.tools.c.viewer.model.ViewerModel;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * adds the given path fragment to the XPath expression upon action
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: XPathFragmentAddingItem.java,v 1.1 2008/02/27 09:34:46 Owner
 *          Exp $
 */
public class XPathFragmentAddingItem extends JMenuItem implements ActionListener
{
	private ViewerModel model;
	private String fragment;

	/**
	 * constructs the item
	 * 
	 * @param caption
	 *            menu item's caption
	 * @param model
	 *            model to refer to
	 * @param fragment
	 *            XPath expression fragment to be added upon action
	 */
	public XPathFragmentAddingItem(String caption, ViewerModel model, String fragment)
	{
		super(caption);
		this.model = model;
		this.fragment = fragment;
		addActionListener(this);
	}

	/**
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent e)
	{
		//add by shen ruoye 2016.1.21
		//在编译xpath的时候，有时绝对路径会有问题，改为相对路径。
		if(fragment.startsWith("/TranslationUnit"))
			fragment=fragment.replace("/TranslationUnit", "./");
		

		model.appendToXPathExpression(fragment, this);
	}
}
