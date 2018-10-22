package softtest.tools.c.viewer.gui;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;
import softtest.tools.c.viewer.util.NLS;

import javax.swing.*;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridLayout;
/**
 * Panel for the XPath entry and editing
 *
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: XPathPanel2.java,v 1.2 2010/03/23 02:48:42 xqing Exp $
 */

public class XPathPanel2 extends JTabbedPane implements ViewerModelListener {
    private ViewerModel model;
    private JTextArea xPathArea;
    private JTextField varName;
    private JTextField vexName;
    private JTextField domainValue;

    /**
     * Constructs the panel
     *
     * @param model model to refer to
     */
    public XPathPanel2(ViewerModel model) {
        super(SwingConstants.BOTTOM);
        this.model = model;
        init(0);
    }
    
    /**
     * Constructs the panel
     *
     * @param model model to refer to
     */
    public XPathPanel2(ViewerModel model, int T) {
        super(SwingConstants.BOTTOM);
        this.model = model;
        init(T);
    }

    private void init(int T) {
        model.addViewerModelListener(this);
        xPathArea = new JTextArea();
        
        
        
        setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(), NLS.nls("XPATH.PANEL.TITLE")));
        if (T==1) {
        	JLabel var = new JLabel("variable  ");
            JLabel vex = new JLabel("vexnode   ");
            
            varName = new JTextField(10);
            vexName = new JTextField(10);
            
            var.setPreferredSize(new Dimension(2,1));
            varName.setPreferredSize(new Dimension(4,1));
                      
            JPanel interval = new JPanel(new GridLayout(2,2));
            interval.add(vex);
            interval.add(vexName);
            interval.add(var);
            interval.add(varName);
            
             //interval.setPreferredSize(new Dimension(2,1));
            //interval.setMaximumSize(new Dimension(2,1));
            //interval.setMinimumSize(new Dimension(2,1));
        	add(interval, NLS.nls("XPATH.PANEL.INTERVAL"));
        	setPreferredSize(new Dimension(200, 30));
        }
        add(new JScrollPane(xPathArea), NLS.nls("XPATH.PANEL.EXPRESSION"));
        add(new EvaluationResultsPanel(model), NLS.nls("XPATH.PANEL.RESULTS"));
        
        xPathArea.setFont(new Font("Arial", Font.PLAIN, 16));
    }

    public String getXPathExpression() {
        return xPathArea.getText();
    }
        
    public String getVexName() {
    	return vexName.getText().replace('\n', '\0');
    }
    
    public String getVarName() {
    	return varName.getText().replace('\n', '\0');
    }

    /**
     * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
     */
    public void viewerModelChanged(ViewerModelEvent e) {
        switch (e.getReason()) {
            case ViewerModelEvent.PATH_EXPRESSION_APPENDED:
                if (e.getSource() != this) {
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