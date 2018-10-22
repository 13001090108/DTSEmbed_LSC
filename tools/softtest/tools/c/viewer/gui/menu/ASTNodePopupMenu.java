package softtest.tools.c.viewer.gui.menu;

import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.gui.menu.ControlFlowGraphItem;

import javax.swing.*;

/**
 * context sensetive menu for the AST Panel
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: ASTNodePopupMenu.java,v 1.5 2010/04/14 01:03:11 liuli Exp $
 */
public class ASTNodePopupMenu extends JPopupMenu
{
	private ViewerModel model;
	private SimpleNode node;

	public ASTNodePopupMenu(ViewerModel model, SimpleNode node)
	{
		this.model = model;
		this.node = node;
		init();
	}

	private void init()
	{
		add(new SimpleNodeSubMenu(model, node));
		addSeparator();
		add(new AttributesSubMenu(model, node));
		if (node instanceof ASTFunctionDefinition || node instanceof ASTNestedFunctionDefinition) {
        	addSeparator();
        	add(new ControlFlowGraphItem(model,node));
        }
		ASTTranslationUnit astroot = (ASTTranslationUnit)model.getRootNode();
		if (node instanceof ASTTranslationUnit && astroot.getCGraph() != null){		
			addSeparator();
        	add(new CallGraphItem(model,node));
		}
	}
}
