package softtest.tools.c.viewer.gui.menu;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.text.MessageFormat;

import javax.swing.JMenuItem;

import softtest.ast.c.SimpleNode;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.util.NLS;

/**
 * @author Liuli
 *2010-4-13
 */
public class CallGraphItem 
		extends JMenuItem
		implements ActionListener{
    private ViewerModel model;
    private SimpleNode node;

    /**
     * constructs the item
     *
     * @param model		model to refer to
     * @param node		MethodDeclaration or ConstructorDeclaration
     */
    public CallGraphItem(ViewerModel model, SimpleNode node) {
    	super(MessageFormat.format(NLS.nls("AST.MENU.CG.IMAGE"), new Object[] { node.toString() }));
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
    	//TODO
    	if (model.genPic(node)) {//genPicÉú³Écg
    		model.fireViewerModelEvent(new ViewerModelEvent(this, ViewerModelEvent.IMAGE_CG_REPAINT));
    	}
    }
}
