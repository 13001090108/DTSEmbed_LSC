package softtest.tools.c.viewer.gui;

import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.tools.c.viewer.gui.menu.ASTNodePopupMenu;
import softtest.tools.c.viewer.model.ASTModel;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;
import softtest.tools.c.viewer.util.NLS;

import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.LinkedList;

/**
 * tree panel GUI
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: ASTPanel.java,v 1.1 2010/01/05 01:48:41 qpeng Exp $
 */

public class ASTPanel extends JPanel implements ViewerModelListener, TreeSelectionListener
{
	private ViewerModel model;
	private JTree tree;

	/**
	 * constructs the panel
	 * 
	 * @param model
	 *            model to attach the panel to
	 */
	public ASTPanel(ViewerModel model)
	{
		this.model = model;
		init();
	}

	private void init()
	{
		model.addViewerModelListener(this);
		setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(), NLS.nls("AST.PANEL.TITLE")));
		setLayout(new BorderLayout());
		tree = new JTree((TreeNode) null);
		tree.addTreeSelectionListener(this);
		tree.addMouseListener(new MouseAdapter()
		{
			public void mouseReleased(MouseEvent e)
			{
				if (e.isPopupTrigger())
				{
					TreePath path = tree.getClosestPathForLocation(e.getX(), e.getY());
					tree.setSelectionPath(path);
					JPopupMenu menu = new ASTNodePopupMenu(model, (SimpleNode) path.getLastPathComponent());
					menu.show(tree, e.getX(), e.getY());
				}
			}
		});

		// Added by Wang Yawen, 2007.12.21
		add(new JScrollPane(tree), BorderLayout.CENTER);
		tree.setFont(new Font("Arial", Font.PLAIN, 16));

	}

	/**
	 * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
	 */
	public void viewerModelChanged(ViewerModelEvent e)
	{
		switch (e.getReason())
		{
		case ViewerModelEvent.CODE_RECOMPILED:
			try {
			tree.setModel(new ASTModel(model.getRootNode()));
			} catch (Exception ex) {
				ex.printStackTrace();
			}
			break;
		case ViewerModelEvent.NODE_SELECTED:
			if (e.getSource() != this)
			{
				LinkedList list = new LinkedList();
				for (Node n = (Node) e.getParameter(); n != null; n = n.jjtGetParent())
				{
					list.addFirst(n);
				}
				TreePath path = new TreePath(list.toArray());
				tree.setSelectionPath(path);
				tree.scrollPathToVisible(path);
			}
			break;
		}
	}

	/**
	 * @see javax.swing.event.TreeSelectionListener#valueChanged(javax.swing.event.TreeSelectionEvent)
	 */
	public void valueChanged(TreeSelectionEvent e)
	{
		if (e.getNewLeadSelectionPath() != null) {
			model.selectNode((SimpleNode) e.getNewLeadSelectionPath().getLastPathComponent(), this);
		}
	}
}
