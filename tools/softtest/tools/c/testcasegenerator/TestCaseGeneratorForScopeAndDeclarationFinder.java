package softtest.tools.c.testcasegenerator;
import javax.swing.*;

import softtest.ast.c.*;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.DumpGraphVisitor;
import softtest.cfg.c.Graph;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;
import softtest.tools.c.jaxen.MatchesFunction;
import softtest.tools.c.viewer.gui.*;
import softtest.tools.c.viewer.model.*;
import softtest.tools.c.viewer.util.NLS;
import softtest.tools.c.viewer.gui.ASTPanel;
import softtest.tools.c.viewer.gui.ImagePanel;
import softtest.tools.c.viewer.gui.SourceCodePanel;
import softtest.tools.c.viewer.gui.XPathPanel;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;

import java.awt.*;
import java.awt.event.*;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.lang.reflect.Method;
/**
 * 变量声明（ScopeAndDeclaration)及表达式类型分析(ExpressionType)的测试用例生成工具使用方法：

 * <p>1、在源代码区输入源代码，Compile后生成抽象语法树；
 * 2、选择需要测试的节点生成相应的XPath表达式，然后Evaluate计算该表达式；
 * 3、确认节点的唯一性之后点击Generate即可生成测试用例代码
 * 4、将生成的测试用例代码拷贝到tests文件夹下的相应测试包内（softtest.test.c.symbol)
 * 5、根据编译平台需求（GCC/KEIL），更改相应的字段</p>
 * @author zys	
 * 2010-3-10
 */
public class TestCaseGeneratorForScopeAndDeclarationFinder {
	
	public static String TEMPDIR="temp";
	private static String CONFIG_FILE = "config/config.ini";
	private final static String NOTE_PREFIX = "#";
	public static int TAB_SIZE=4;
	public static void main(String[] args) {
		TestCaseGeneratorForScopeAndDeclarationFinder v=new TestCaseGeneratorForScopeAndDeclarationFinder();
		String srcFileType=v.initFileType();
		System.out.println("Now the Parser is processing "+srcFileType+" type sourcefile.");
		MatchesFunction.registerSelfInSimpleContext();
		 new MainFrame3(); 
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

class MainFrame3 extends JFrame implements ActionListener,
		ActionCommands, ViewerModelListener {
	private static final long serialVersionUID = 1L;

	private ViewerModel model;

	private SourceCodePanel sourcePanel;
	
	private TestCasePanel1 testcasePanel;

	private ASTPanel astPanel;
	
	private ImagePanel imagePanel;

	private XPathPanel xPathPanel;

	private JTabbedPane astANDcfg;
	
	private JButton compileBtn;
	
	private JButton testcaseBtn;

	private JButton evalBtn;

	private JLabel statusLbl;

	/**
	 * constructs and shows the frame
	 */
	public MainFrame3() {
		super(NLS.nls("MAIN.FRAME.TITLE.SCOPEANDDECLARATIONFINDER"));
		init();
	}

	private void init() {
		model = new ViewerModel();
		model.addViewerModelListener(this);
		sourcePanel = new SourceCodePanel(model);
		astPanel = new ASTPanel(model);
		xPathPanel = new XPathPanel(model);
		testcasePanel = new TestCasePanel1(model);
		imagePanel = new ImagePanel(model,NLS.nls("IMAGE.PANEL.TITLE"));
		getContentPane().setLayout(new BorderLayout());
		
		astANDcfg = new JTabbedPane(SwingConstants.LEFT, JTabbedPane.SCROLL_TAB_LAYOUT);
		astANDcfg.add(astPanel,"AST");
		astANDcfg.add(imagePanel,"CFG");
		
		JSplitPane editingPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				sourcePanel, astANDcfg);
		editingPane.setResizeWeight(0.5d);
		
		JSplitPane resultPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
				xPathPanel, testcasePanel);
		resultPane.setResizeWeight(0.5d);
		
		JSplitPane interactionsPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
				editingPane,resultPane);
		//interactionsPane.add(resultPane, BorderLayout.SOUTH);
		//interactionsPane.add(editingPane, BorderLayout.CENTER);
		interactionsPane.setResizeWeight(0.75d);
		
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
		setSize(800, 600);
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
		//astroot.jjtAccept(new ControlFlowVisitor(), null);
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
		for(int i=0;i<TestCaseGeneratorForScopeAndDeclarationFinder.TAB_SIZE*times;i++){
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
		tb.append("\"all\"\n");
		
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		tb.append("\"" + xPathPanel.getXPathExpression() + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		
		String typestring = "null";
		if (model.getLastEvaluationResults() != null && model.getLastEvaluationResults().size() > 0) {
			for (Object obj : model.getLastEvaluationResults()) {
				SimpleNode eb = (SimpleNode) obj;
				Method m;
				try {
					m = eb.getClass().getMethod("getType");
					if(m!=null){
						CType type=(CType) m.invoke(eb);
						if(type!=null){
							typestring=type.toString();
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				} 				
				break;
			}
		}
		
		tb.append("\"" + typestring + "\"\n");
		appendTab(tb, 3);
		tb.append(",\n");
		appendTab(tb, 3);
		tb.append("},\n");
		testcasePanel.setTestCase(tb.toString());
	}
	
}

class TestCasePanel1 extends JPanel implements ViewerModelListener {
	private JTextArea testCaseArea;
	private ViewerModel model;
	public TestCasePanel1(ViewerModel model){
		this.model = model;
		init();
	}
	private void init() {
		model.addViewerModelListener(this);
		testCaseArea = new JTextArea();
		setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(), "测试用例"));
        setLayout(new BorderLayout());
        
        add(new JScrollPane(testCaseArea), BorderLayout.CENTER);
        testCaseArea.setFont(new Font("Courier new", Font.PLAIN, 16));
        testCaseArea.setTabSize(TestCaseGeneratorForScopeAndDeclarationFinder.TAB_SIZE);

        setPreferredSize(new Dimension(-1, 200));
	}
	
	public void clearTestCase(){
		testCaseArea.setText("");
	}
	
	public void setTestCase(String str){
		testCaseArea.setText(str);
	}
	
    public String getTestCase() {
        return testCaseArea.getText();
    }
    
    /**
     * @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
     */
    public void viewerModelChanged(ViewerModelEvent e) {
        switch (e.getReason()) {
            case ViewerModelEvent.PATH_EXPRESSION_APPENDED:
                if (e.getSource() != this) {
                   // xPathArea.append((String) e.getParameter());
                }
              //  setSelectedIndex(0);
                break;
            case ViewerModelEvent.CODE_RECOMPILED:
             //   setSelectedIndex(0);
                break;
        }
    }
}