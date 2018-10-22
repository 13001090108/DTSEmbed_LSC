package softtest.tools.c.testcasegenerator;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import java.util.List;
import javax.swing.*;
import softtest.ast.c.*;
import softtest.cfg.c.*;
import softtest.domain.c.analysis.ControlFlowDomainVisitor;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.*;
import softtest.tools.c.jaxen.MatchesFunction;
import softtest.tools.c.viewer.gui.*;
import softtest.tools.c.viewer.model.*;
import softtest.tools.c.viewer.util.*;
import softtest.config.c.*;


public class TestCaseGeneratorForDomain {
	
	public static String TEMPDIR="temp";
	private static String CONFIG_FILE = "config/config.ini";
	private final static String NOTE_PREFIX = "#";
	public static int TAB_SIZE=4;
	public static void main(String[] args) {
		TestCaseGeneratorForControlFlowVisitor v=new TestCaseGeneratorForControlFlowVisitor();
		String srcFileType=v.initFileType();
		System.out.println("Now the Parser is processing "+srcFileType+" type sourcefile.");
		Config.DUMP_DOMAIN=true;
		Config.DUMP_SYMBOL=true;
		MatchesFunction.registerSelfInSimpleContext();
		 new MainFrame2(); 
	}
	public String initFileType()
	{
		File configFile = new File(CONFIG_FILE);
		if (configFile.exists())
		{
			try
			{
				BufferedReader reader = new BufferedReader(new FileReader(
						configFile));
				String config;
				while ((config = reader.readLine()) != null)
				{
					if (config.trim().startsWith(NOTE_PREFIX) || config.trim().startsWith("-I")
							|| config.trim().startsWith("-D"))
					{
						continue;
					}
					if (config.trim().equalsIgnoreCase("-gcc"))
					{
						CParser.setType("gcc");
						return "gcc";
					} else if (config.trim().equalsIgnoreCase("-keil"))
					{
						CParser.setType("keil");
						return "keil";
					}
				}
			} catch (Exception e)
			{
				System.err.println("Error in reading the config file.");
				e.printStackTrace();
				return null;
			}
		}
		return null;
	}
}

class MainFrame2 extends JFrame implements ActionListener,
		ActionCommands, ViewerModelListener {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private ViewerModel model;

	private SourceCodePanel sourcePanel;
	
	private TestCasePanel6 testcasePanel;

	private ASTPanel astPanel;
	
	private ImagePanel imagePanel;

	private XPathPanel2 xPathPanel;
	
	private JTabbedPane astANDcfg;

	private JButton compileBtn;
	
	private JButton testcaseBtn;

	private JButton evalBtn;

	private JLabel statusLbl;

	/**
	 * constructs and shows the frame
	 */
	public MainFrame2() {
		super(NLS.nls("MAIN.FRAME.TITLE.DOMAIN"));
		init();
	}

	private void init() {
		model = new ViewerModel();
		model.addViewerModelListener(this);
		sourcePanel = new SourceCodePanel(model);
		astPanel = new ASTPanel(model);
		xPathPanel = new XPathPanel2(model,1);
		testcasePanel = new TestCasePanel6(model);
		imagePanel = new ImagePanel(model,NLS.nls("IMAGE.PANEL.TITLE"));
		getContentPane().setLayout(new BorderLayout());
		
		astANDcfg = new JTabbedPane(SwingConstants.LEFT, JTabbedPane.SCROLL_TAB_LAYOUT);
		astANDcfg.add(astPanel,"AST");
		astANDcfg.add(imagePanel,"CFG");
		
		JSplitPane editingPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				sourcePanel, astANDcfg);
		editingPane.setResizeWeight(0.42d);
		
		JSplitPane resultPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				xPathPanel, testcasePanel);
		resultPane.setResizeWeight(0.2d);
		
		JSplitPane interactionsPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
				editingPane,resultPane);
		//interactionsPane.add(resultPane, BorderLayout.SOUTH);
		//interactionsPane.add(editingPane, BorderLayout.CENTER);
		interactionsPane.setResizeWeight(0.79d);
		//interactionsPane.setMaximumSize(new Dimension(100,20));
		
		getContentPane().add(interactionsPane, BorderLayout.CENTER);
		
		compileBtn = new JButton(NLS.nls("MAIN.FRAME.COMPILE_BUTTON.TITLE"));
		compileBtn.setActionCommand(COMPILE_ACTION);
		compileBtn.addActionListener(this);
		evalBtn = new JButton(NLS.nls("MAIN.FRAME.EVALUATE_BUTTON.TITLE"));
		evalBtn.setActionCommand(EVALUATE_ACTION);
		evalBtn.addActionListener(this);
		evalBtn.setEnabled(false);
		testcaseBtn = new JButton("Generate");
		testcaseBtn.setActionCommand("Generate");
		testcaseBtn.addActionListener(this);
		testcaseBtn.setEnabled(false);
		statusLbl = new JLabel();
		statusLbl.setHorizontalAlignment(SwingConstants.RIGHT);
		JPanel btnPane = new JPanel(new FlowLayout(FlowLayout.LEFT));
		btnPane.add(compileBtn);
		btnPane.add(evalBtn);
		btnPane.add(testcaseBtn);
		btnPane.add(statusLbl);
		getContentPane().add(btnPane, BorderLayout.SOUTH);

		compileBtn.setFont(new Font("Arial", Font.PLAIN, 16));
		evalBtn.setFont(new Font("Arial", Font.PLAIN, 16));
		statusLbl.setFont(new Font("Arial", Font.PLAIN, 16));

		setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		pack();
		setSize(1024, 768);
		setVisible(true);
	}

	public void compile(String source) {
		ASTTranslationUnit astroot = (ASTTranslationUnit)model.getRootNode();
		//	产生符号表
		ScopeAndDeclarationFinder v=new ScopeAndDeclarationFinder();
		astroot.jjtAccept(v, null);
		OccurrenceAndExpressionTypeFinder ov=new OccurrenceAndExpressionTypeFinder();
		astroot.jjtAccept(ov, null);
		
		// 产生控制流图
		astroot.jjtAccept(new ControlFlowVisitor(), null);
		
		//zys:确保每次符号生成时的序号稳定性
		SymbolFactor.resetNameCount();
		astroot.jjtAccept(new ControlFlowDomainVisitor(), null);
	}
		
	/**
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent e) {
		String command = e.getActionCommand();
		long t0, t1;
		if (command.equals(COMPILE_ACTION)) {
			t0 = System.currentTimeMillis();
			model.commitSource(sourcePanel.getSourceCode());
			compile(sourcePanel.getSourceCode());
			t1 = System.currentTimeMillis();
			setStatus(NLS.nls("MAIN.FRAME.COMPILATION.TOOK") + " " + (t1 - t0)
					+ " ms");
		} else if (command.equals(EVALUATE_ACTION)) {
			try {
				t0 = System.currentTimeMillis();
				model.evaluateXPathExpression(xPathPanel.getXPathExpression(),this);
				t1 = System.currentTimeMillis();
				setStatus(NLS.nls("MAIN.FRAME.EVALUATION.TOOK") + " "
						+ (t1 - t0) + " ms");
			} catch (Exception exc) {
				setStatus(NLS.nls("MAIN.FRAME.EVALUATION.PROBLEM") + " "
						+ exc.toString());
				new ParseExceptionHandler(this, exc);
			}
		} else if (command.equals("Generate")) {
			try {
				t0 = System.currentTimeMillis();
				//model.evaluateXPathExpression(xPathPanel.getXPathExpression(),this);
				generateTestCase();
				t1 = System.currentTimeMillis();
				setStatus("Generation took " + (t1 - t0) + " ms");
			} catch (Exception exc) {
				setStatus("Generate failed "+exc.toString());
				new ParseExceptionHandler(this, exc);
			}
		}
	}

	/**
	 * Sets the status bar message
	 * 
	 * @param string
	 *            the new status, the empty string will be set if the value is
	 *            <code>null</code>
	 */
	private void setStatus(String string) {
		statusLbl.setText(string == null ? "" : string);
	}

	/**
	 * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
	 */
	public void viewerModelChanged(ViewerModelEvent e) {
		
		switch (e.getReason()) {
    		case ViewerModelEvent.CODE_RECOMPILED:
    			evalBtn.setEnabled(model.hasCompiledTree());
    			testcaseBtn.setEnabled(model.hasCompiledTree());
    			astANDcfg.setEnabledAt(1, false);
    			astANDcfg.setSelectedIndex(0);
    			break;
    		case ViewerModelEvent.IMAGE_REPAINT:
    			//tree.setModel(new ASTModel(model.getRootNode()));
    			astANDcfg.setEnabledAt(1, true);
    			astANDcfg.setSelectedIndex(1);
    			
    			
    			break;
		}
	}
	
	private void appendTab(StringBuffer tb, int times){
		for(int i=0;i<TestCaseGeneratorForDomain.TAB_SIZE*times;i++){
			tb.append(" ");
		}
	}

	private void appendSpace(StringBuffer tb, int times){
		for(int i=0;i<times;i++){
			tb.append(" ");
		}
	}
	
	private void generateTestCase() {
		testcasePanel.clearTestCase();
		String str = sourcePanel.getSourceCode();
		StringBuffer tb = new StringBuffer("");
		tb.append("/////////////////  0   ///////////////////	\n");
		appendTab(tb, 3);
		tb.append("{\n");

		String[] lines = str.split("\n");
		for (int i = 0; i < lines.length; i++) {
			appendTab(tb, 3);
			tb.append("\"");
			String temp = lines[i];
			temp = temp.replace("\\", "\\\\");
			temp = temp.replace("\"", "\\\"");

			tb.append(temp);
			tb.append("\"");

			if (lines[i].length() <= 100) {
				appendSpace(tb, 69 - lines[i].length());
			}
			if (i < lines.length - 1) {
				tb.append("+\"\\n\"+\n");
			} else {
				tb.append("\n");
			}
		}
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		tb.append("\"" + xPathPanel.getVexName() + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		tb.append("\"" + xPathPanel.getVarName() + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		
		List mds = model.getRootNode().findChildrenOfType(ASTFunctionDefinition.class);
		String value = "ERROR";
		if (!mds.isEmpty()) {
			Graph g = ((ASTFunctionDefinition)mds.get(0)).getGraph();
			VexNode vn = g.nodes.get(xPathPanel.getVexName());
			Hashtable<VariableNameDeclaration, Expression> vTable=vn.getValueSet().getTable();
			for (VariableNameDeclaration vv : vTable.keySet()) {
				if (vv.getImage().equals(xPathPanel.getVarName())) {
					Expression e = vTable.get(vv);
					if (e != null) {
						value = e.toString();
					}
					break;
				}
			}
		}
		
		tb.append("\"" + value + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		
		value = "ERROR";
		if (!mds.isEmpty()) {
			Graph g = ((ASTFunctionDefinition)mds.get(0)).getGraph();
			VexNode vn = g.nodes.get(xPathPanel.getVexName());
			Hashtable<VariableNameDeclaration, Expression> vTable=vn.getValueSet().getTable();
			Domain dm = null;
			for (VariableNameDeclaration vv : vTable.keySet()) {
				if (vv.getImage().equals(xPathPanel.getVarName())) {
					dm=vn.getDomain(vv);
					break;
				}
			}
			if (dm != null) {
				value = dm.toString();
			}
		}
		
		tb.append("\"" + value + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		tb.append("},\n");
		testcasePanel.setTestCase(tb.toString());
	}
}

class TestCasePanel6 extends JPanel implements ViewerModelListener
{
	private JTextArea testCaseArea;
	private ViewerModel model;
	public TestCasePanel6(ViewerModel model)
	{
		this.model = model;
		init();
	}
	private void init()
	{
		model.addViewerModelListener(this);
		testCaseArea = new JTextArea();
		setBorder(BorderFactory.createTitledBorder(BorderFactory
				.createEtchedBorder(), "测试用例"));
		setLayout(new BorderLayout());

		add(new JScrollPane(testCaseArea), BorderLayout.CENTER);
		testCaseArea.setFont(new Font("Courier new", Font.PLAIN, 16));
		testCaseArea
				.setTabSize(TestCaseGeneratorForControlFlowVisitor.TAB_SIZE);

		setPreferredSize(new Dimension(-1, 200));
	}

	public void clearTestCase()
	{
		testCaseArea.setText("");
	}

	public void setTestCase(String str)
	{
		testCaseArea.setText(str);
	}

	public String getTestCase()
	{
		return testCaseArea.getText();
	}

	/**
	 * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
	 */
	public void viewerModelChanged(ViewerModelEvent e)
	{
		switch (e.getReason())
		{
			case ViewerModelEvent.PATH_EXPRESSION_APPENDED :
				if (e.getSource() != this)
				{
					// xPathArea.append((String) e.getParameter());
				}
				//  setSelectedIndex(0);
				break;
			case ViewerModelEvent.CODE_RECOMPILED :
				//   setSelectedIndex(0);
				break;
		}
	}
}
