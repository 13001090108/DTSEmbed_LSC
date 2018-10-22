package softtest.tools.c.testcasegenerator;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.SwingConstants;
import javax.swing.WindowConstants;

import softtest.DefUseAnalysis.c.DUAnalysisVisitor;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CParser;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.callgraph.c.DumpCGraphVisitor;
import softtest.cfg.c.ControlFlowData;
import softtest.cfg.c.ControlFlowVisitor;
import softtest.cfg.c.Graph;
import softtest.config.c.Config;
import softtest.fsmanalysis.c.FSMAnalysisVisitor;
import softtest.fsmanalysis.c.FSMControlFlowData;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.tools.c.jaxen.MatchesFunction;
import softtest.tools.c.viewer.gui.ASTPanel;
import softtest.tools.c.viewer.gui.ActionCommands;
import softtest.tools.c.viewer.gui.ImagePanel;
import softtest.tools.c.viewer.gui.ParseExceptionHandler;
import softtest.tools.c.viewer.gui.SourceCodePanel;
import softtest.tools.c.viewer.gui.XPathPanel;
import softtest.tools.c.viewer.model.ViewerModel;
import softtest.tools.c.viewer.model.ViewerModelEvent;
import softtest.tools.c.viewer.model.ViewerModelListener;
import softtest.tools.c.viewer.util.NLS;

public class TestCaseGeneratorForRules {
	
	private static String CONFIG_FILE = "config/config.ini";
	private final static String NOTE_PREFIX = "#";
	public static int TAB_SIZE = 4;

	public static void main(String[] args)
	{
		TestCaseGeneratorForRules v = new TestCaseGeneratorForRules();
		String srcFileType = v.initFileType();
		System.out.println("Now the Parser is processing " + srcFileType
				+ " type sourcefile.");
		MatchesFunction.registerSelfInSimpleContext();
		new MainFrame7();
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
					if (config.trim().startsWith(NOTE_PREFIX)
							|| config.trim().startsWith("-I")
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

class MainFrame7 extends JFrame
implements
	ActionListener,
	ActionCommands,
	ViewerModelListener
{
private static final long serialVersionUID = 1L;

private ViewerModel model;

private SourceCodePanel sourcePanel;

private TestCasePanel4 testcasePanel;

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
public MainFrame7()
{
super(NLS.nls("MAIN.FRAME.TITLE.RULES"));
init();
}

private void init()
{
model = new ViewerModel();
model.addViewerModelListener(this);
sourcePanel = new SourceCodePanel(model);
astPanel = new ASTPanel(model);
xPathPanel = new XPathPanel(model);
testcasePanel = new TestCasePanel4(model);
imagePanel = new ImagePanel(model,NLS.nls("IMAGE.PANEL.TITLE"));
getContentPane().setLayout(new BorderLayout());

astANDcfg = new JTabbedPane(SwingConstants.LEFT,
		JTabbedPane.SCROLL_TAB_LAYOUT);
astANDcfg.add(astPanel, "AST");
astANDcfg.add(imagePanel, "CFG");

JSplitPane editingPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
		sourcePanel, astANDcfg);
editingPane.setResizeWeight(0.5d);

JSplitPane resultPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
		xPathPanel, testcasePanel);
resultPane.setResizeWeight(0.5d);

JSplitPane interactionsPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
		editingPane, resultPane);
// interactionsPane.add(resultPane, BorderLayout.SOUTH);
// interactionsPane.add(editingPane, BorderLayout.CENTER);
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

public void compile(String source)
{
ASTTranslationUnit astroot = (ASTTranslationUnit) model.getRootNode();
// 产生符号表
ScopeAndDeclarationFinder v = new ScopeAndDeclarationFinder();
astroot.jjtAccept(v, null);
OccurrenceAndExpressionTypeFinder ov = new OccurrenceAndExpressionTypeFinder();
astroot.jjtAccept(ov, null);

// 产生控制流图
astroot.jjtAccept(new ControlFlowVisitor(), null);

//产生函数调用图
CGraph g = new CGraph();
((AbstractScope)(astroot.getScope())).resolveCallRelation(g);
List<CVexNode> list = g.getTopologicalOrderList();
Collections.reverse(list);
dump(g, list);

// 产生定义使用链DU
astroot.jjtAccept(new DUAnalysisVisitor(), null);

//自动机分析
FSMControlFlowData data=new FSMControlFlowData();
astroot.jjtAccept(new FSMAnalysisVisitor(data), data);
}

private void dump(CGraph g, List<CVexNode> list) {
	if (Config.TRACE) 
	{
		for(CVexNode n:list){
			System.out.print(n.getName()+"  ");
		}
	
		String name ="temp/TestCaseGenerator_CallGraph";
		g.accept(new DumpCGraphVisitor(), name + ".dot");
		System.out.println("文件内函数调用关系图输出到了文件" + name + ".dot");
		try {
			java.lang.Runtime.getRuntime().exec("dot -Tjpg -o " + name + ".jpg " + name + ".dot").waitFor();
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2) {
			System.out.println(e2);
		}
		System.out.println("文件内函数调用关系图打印到了文件" + name + ".jpg");
	}
}
/**
* @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
*/
public void actionPerformed(ActionEvent e)
{
String command = e.getActionCommand();
long t0, t1;
if (command.equals(COMPILE_ACTION))
{
	t0 = System.currentTimeMillis();
	model.commitSource(sourcePanel.getSourceCode());
	compile(sourcePanel.getSourceCode());
	t1 = System.currentTimeMillis();
	setStatus(NLS.nls("MAIN.FRAME.COMPILATION.TOOK") + " " + (t1 - t0)
			+ " ms");
} else if (command.equals(EVALUATE_ACTION))
{
	try
	{
		t0 = System.currentTimeMillis();
		model.evaluateXPathExpression(xPathPanel.getXPathExpression(),
				this);
		t1 = System.currentTimeMillis();
		setStatus(NLS.nls("MAIN.FRAME.EVALUATION.TOOK") + " "
				+ (t1 - t0) + " ms");
	} catch (Exception exc)
	{
		setStatus(NLS.nls("MAIN.FRAME.EVALUATION.PROBLEM") + " "
				+ exc.toString());
		new ParseExceptionHandler(this, exc);
	}
} else if (command.equals("Generate"))
{
	try
	{
		t0 = System.currentTimeMillis();
		// model.evaluateXPathExpression(xPathPanel.getXPathExpression(),this);
		generateTestCase();
		t1 = System.currentTimeMillis();
		setStatus("Generation took " + (t1 - t0) + " ms");
	} catch (Exception exc)
	{
		setStatus("Generate failed " + exc.toString());
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
private void setStatus(String string)
{
statusLbl.setText(string == null ? "" : string);
}

/**
* @see ViewerModelListener#viewerModelChanged(ViewerModelEvent)
*/
public void viewerModelChanged(ViewerModelEvent e)
{
switch (e.getReason())
{
	case ViewerModelEvent.CODE_RECOMPILED :
		evalBtn.setEnabled(model.hasCompiledTree());
		testcaseBtn.setEnabled(model.hasCompiledTree());
		astANDcfg.setEnabledAt(1, false);
		astANDcfg.setSelectedIndex(0);
		break;
	case ViewerModelEvent.IMAGE_REPAINT :
		// tree.setModel(new ASTModel(model.getRootNode()));
		astANDcfg.setEnabledAt(1, true);
		astANDcfg.setSelectedIndex(1);
		break;
}
}

private void appendTab(StringBuffer tb, int times)
{
for (int i = 0; i < TestCaseGeneratorForControlFlowVisitor.TAB_SIZE
		* times; i++)
{
	tb.append(" ");
}
}

private void appendSpace(StringBuffer tb, int times)
{
for (int i = 0; i < times; i++)
{
	tb.append(" ");
}
}

private void generateTestCase()
{
testcasePanel.clearTestCase();
String str = sourcePanel.getSourceCode();
StringBuffer tb = new StringBuffer("");
tb.append("/////////////////  0   ///////////////////	\n");
appendTab(tb, 3);
tb.append("{\n");

String[] lines = str.split("\n");
for (int i = 0; i < lines.length; i++)
{
	appendTab(tb, 3);
	tb.append("\"");
	String temp = lines[i];
	temp = temp.replace("\\", "\\\\");
	temp = temp.replace("\"", "\\\"");

	tb.append(temp);
	tb.append("\"");

	if (lines[i].length() <= 100)
	{
		appendSpace(tb, 69 - lines[i].length());
	}
	if (i < lines.length - 1)
	{
		tb.append("+\"\\n\"+\n");
	} else
	{
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
tb.append("\"" + "OK" + "\"\n");
appendTab(tb, 3);
tb.append(",\n");
appendTab(tb, 3);
tb.append("},\n");
testcasePanel.setTestCase(tb.toString());
}

}

class TestCasePanel4 extends JPanel implements ViewerModelListener
{
	private JTextArea testCaseArea;
	private ViewerModel model;
	public TestCasePanel4(ViewerModel model)
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