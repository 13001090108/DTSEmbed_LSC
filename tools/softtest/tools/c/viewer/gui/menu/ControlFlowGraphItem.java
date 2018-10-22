package softtest.tools.c.viewer.gui.menu;
import javax.swing.*;

import softtest.ast.c.*;
import softtest.tools.c.jaxen.Attribute;
import softtest.tools.c.jaxen.AttributeAxisIterator;
import softtest.tools.c.viewer.model.AttributeToolkit;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.util.NLS;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.text.MessageFormat;


/**
 * adds the given path fragment to the XPath expression upon action
 * open the control flow graph image about the node
 *
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: ControlFlowGraphItem.java,v 1.1 2010/01/11 01:26:36 qpeng Exp $
 */
public class ControlFlowGraphItem
        extends JMenuItem
        implements ActionListener {
    private ViewerModel model;
    private SimpleNode node;

    /**
     * constructs the item
     *
     * @param model		model to refer to
     * @param node		MethodDeclaration or ConstructorDeclaration
     */
    public ControlFlowGraphItem(ViewerModel model, SimpleNode node) {
    	super(MessageFormat.format(NLS.nls("AST.MENU.CFG.IMAGE"), new Object[]{node.toString()}));
        this.model = model;
        this.node = node;
        //init();
        addActionListener(this);
	}
    
    /*
    private void init() {
        AttributeAxisIterator i = new AttributeAxisIterator(node);
        while (i.hasNext()) {
            Attribute attribute = (Attribute) i.next();
            add(new XPathFragmentAddingItem(attribute.getName() + " = " + attribute.getValue(), model,
                    AttributeToolkit.constructPredicate(attribute)));
        }
    }
    */

	/**
     * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
     */
    public void actionPerformed(ActionEvent e) {
        //model.appendToXPathExpression(fragment, this);
    	if (model.genPic(node)) {
    		model.fireViewerModelEvent(new ViewerModelEvent(this, ViewerModelEvent.IMAGE_REPAINT));
    	}
    }
}
