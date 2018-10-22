package softtest.tools.c.viewer.gui;

import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;
import softtest.tools.c.viewer.util.NLS;

import javax.swing.*;

import java.awt.Dimension;
import java.awt.Font;

/**
 * Panel for the XPath entry and editing
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: XPathPanel.java,v 1.1 2010/01/05 01:48:41 qpeng Exp $
 */

public class XPathPanel extends JTabbedPane implements ViewerModelListener
{
	private ViewerModel model;
	private JTextArea xPathArea;

	/**
	 * Constructs the panel
	 * 
	 * @param model
	 *            model to refer to
	 */
	public XPathPanel(ViewerModel model)
	{
		super(SwingConstants.BOTTOM);
		this.model = model;
		init();
	}

	private void init()
	{
		model.addViewerModelListener(this);
		xPathArea = new JTextArea();
		setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(), NLS.nls("XPATH.PANEL.TITLE")));
		add(new JScrollPane(xPathArea), NLS.nls("XPATH.PANEL.EXPRESSION"));
		add(new EvaluationResultsPanel(model), NLS.nls("XPATH.PANEL.RESULTS"));
		setPreferredSize(new Dimension(-1, 200));

		// Added by Wang Yawen, 2007.12.21
		xPathArea.setFont(new Font("Arial", Font.PLAIN, 16));

	}

	public String getXPathExpression()
	{
		return xPathArea.getText();
	}

	/**
	 * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
	 */
	public void viewerModelChanged(ViewerModelEvent e)
	{
		switch (e.getReason())
		{
		case ViewerModelEvent.PATH_EXPRESSION_APPENDED:
			if (e.getSource() != this)
			{
				xPathArea.append((String) e.getParameter());
			}
			setSelectedIndex(0);
			break;
		case ViewerModelEvent.CODE_RECOMPILED:
			setSelectedIndex(0);
			break;
		}
	}
}