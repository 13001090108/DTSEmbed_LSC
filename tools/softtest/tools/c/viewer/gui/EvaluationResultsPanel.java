package softtest.tools.c.viewer.gui;

import softtest.ast.c.SimpleNode;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import java.awt.BorderLayout;
import java.awt.Font;
import java.util.Vector;

/**
 * A panel showing XPath expression evaluation results
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: EvaluationResultsPanel.java,v 1.1 2010/01/05 01:48:41 qpeng Exp $
 */
public class EvaluationResultsPanel extends JPanel implements ViewerModelListener
{
	private ViewerModel model;
	private JList list;

	/**
	 * constructs the panel
	 * 
	 * @param model
	 *            model to refer to
	 */
	public EvaluationResultsPanel(ViewerModel model)
	{
		super(new BorderLayout());

		this.model = model;

		init();
	}

	private void init()
	{
		model.addViewerModelListener(this);

		list = new JList();
		list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);

		list.addListSelectionListener(new ListSelectionListener()
		{
			public void valueChanged(ListSelectionEvent e)
			{
				if (list.getSelectedValue() != null)
				{
					model.selectNode((SimpleNode) list.getSelectedValue(), EvaluationResultsPanel.this);
				}
			}
		});

		// Added by Wang Yawen, 2007.12.21
		add(new JScrollPane(list), BorderLayout.CENTER);
		list.setFont(new Font("Arial", Font.PLAIN, 14));

	}

	/**
	 * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
	 */
	public void viewerModelChanged(ViewerModelEvent e)
	{
		switch (e.getReason())
		{
		case ViewerModelEvent.PATH_EXPRESSION_EVALUATED:

			if (e.getSource() != this)
			{
				list.setListData(new Vector(model.getLastEvaluationResults()));
			}

			break;

		case ViewerModelEvent.CODE_RECOMPILED:
			list.setListData(new Vector(0));

			break;
		}
	}
}
