package softtest.tools.c.viewer.gui.menu;

import softtest.ast.c.SimpleNode;
import softtest.tools.c.jaxen.Attribute;
import softtest.tools.c.jaxen.AttributeAxisIterator;
import softtest.tools.c.viewer.model.AttributeToolkit;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.util.NLS;

import javax.swing.*;
import java.text.MessageFormat;

/**
 * contains menu items for the predicate creation
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: AttributesSubMenu.java,v 1.1 2010/01/05 01:48:54 qpeng Exp $
 */
public class AttributesSubMenu extends JMenu
{
	private ViewerModel model;
	private SimpleNode node;

	public AttributesSubMenu(ViewerModel model, SimpleNode node)
	{
		super(MessageFormat.format(NLS.nls("AST.MENU.ATTRIBUTES"), new Object[] { node.toString() }));
		this.model = model;
		this.node = node;
		init();
	}

	private void init()
	{
		AttributeAxisIterator i = new AttributeAxisIterator(node);
		while (i.hasNext())
		{
			Attribute attribute = (Attribute) i.next();
			add(new XPathFragmentAddingItem(attribute.getName() + " = " + attribute.getValue(), model,
					AttributeToolkit.constructPredicate(attribute)));
		}
	}
}
