package softtest.tools.c.viewer.gui.menu;

import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.util.NLS;

import javax.swing.*;
import java.text.MessageFormat;

/**
 * submenu for the simple node itself
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: SimpleNodeSubMenu.java,v 1.1 2010/01/05 01:48:54 qpeng Exp $
 */
public class SimpleNodeSubMenu extends JMenu
{
	private ViewerModel model;
	private SimpleNode node;

	/**
	 * constructs the submenu
	 * 
	 * @param model
	 *            model to which the actions will be forwarded
	 * @param node
	 *            menu's owner
	 */
	public SimpleNodeSubMenu(ViewerModel model, SimpleNode node)
	{
		super(MessageFormat.format(NLS.nls("AST.MENU.NODE.TITLE"), new Object[] { node.toString() }));
		this.model = model;
		this.node = node;
		init();
	}

	private void init()
	{
		StringBuffer buf = new StringBuffer(200);
		for (Node temp = node; temp != null; temp = temp.jjtGetParent())
		{
			buf.insert(0, "/" + temp.toString());
		}
		add(new XPathFragmentAddingItem(NLS.nls("AST.MENU.NODE.ADD_ABSOLUTE_PATH"), model, buf.toString()));
		add(new XPathFragmentAddingItem(NLS.nls("AST.MENU.NODE.ADD_ALLDESCENDANTS"), model, "//" + node.toString()));
	}
}
