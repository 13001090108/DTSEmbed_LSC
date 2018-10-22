package softtest.tools.c.viewer.model;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import softtest.ast.c.*;
import softtest.callgraph.c.CGraph;
import softtest.callgraph.c.CVexNode;
import softtest.callgraph.c.DumpCGraphVisitor;
import softtest.cfg.c.*;
import softtest.symboltable.c.AbstractScope;
import softtest.symboltable.c.OccurrenceAndExpressionTypeFinder;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.tools.c.jaxen.DocumentNavigator;
import softtest.tools.c.testcasegenerator.TestCaseGeneratorForScopeAndDeclarationFinder;
import softtest.tools.c.viewer.model.ViewerModelEvent;

import org.jaxen.BaseXPath;
import org.jaxen.JaxenException;
import org.jaxen.XPath;

public class ViewerModel
{

	private List listeners;
	private SimpleNode rootNode;
	private List evaluationResults;
	private String		image;
	
	public ViewerModel()
	{
		listeners = new ArrayList(5);
	}

	public SimpleNode getRootNode()
	{
		return rootNode;
	}

	/**
	 * commits source code to the model. all existing source will be replaced
	 */
	public void commitSource(String source)
	{
		try{
//			ASTTranslationUnit translationUnit = CParser.createAST(new StringReader(source));
			CCharStream ccs = new CCharStream(new StringReader(source));
			CParser parser=CParser.getParser(ccs);
			rootNode =parser.TranslationUnit();
			fireViewerModelEvent(new ViewerModelEvent(this, ViewerModelEvent.CODE_RECOMPILED));
		}catch(ParseException e)
		{
			e.printStackTrace();
		}
	}
	
	public String getImagePath() {
    	return image;
    }

	/**
	 * determines whether the model has a compiled tree at it's disposal
	 * 
	 * @return true if there is an AST, false otherwise
	 */
	public boolean hasCompiledTree()
	{
		return rootNode != null;
	}

	/**
	 * evaluates the given XPath expression against the current tree
	 * 
	 * @param xPath
	 *            XPath expression to be evaluated
	 * @param evaluator
	 *            object which requests the evaluation
	 */
	public void evaluateXPathExpression(String xPath, Object evaluator) throws ParseException, JaxenException
	{
		XPath xpath = new BaseXPath(xPath, new DocumentNavigator());
		evaluationResults = xpath.selectNodes(rootNode);
		fireViewerModelEvent(new ViewerModelEvent(evaluator, ViewerModelEvent.PATH_EXPRESSION_EVALUATED));
	}

	/**
	 * retrieves the results of last evaluation
	 * 
	 * @return a list containing the nodes selected by the last XPath expression
	 *         <p/> evaluation
	 */
	public List getLastEvaluationResults()
	{
		return evaluationResults;
	}

	/**
	 * selects the given node in the AST
	 * 
	 * @param node
	 *            node to be selected
	 * @param selector
	 *            object which requests the selection
	 */
	public void selectNode(SimpleNode node, Object selector)
	{
		fireViewerModelEvent(new ViewerModelEvent(selector, ViewerModelEvent.NODE_SELECTED, node));
	}

	public File createTempDirectory(String temp)
	{
		if(temp==null || temp.length()==0)
		{
			throw new RuntimeException("Create Temp Directory: "+temp+" Failed!");
		}
		File dir=new File(temp);
		if(!dir.exists())
		{
			dir.mkdir();
		}
		return dir;
	}
	
	public File createTempFile(String dir,String fileName)
	{
		File directory=createTempDirectory(dir);
		if(!directory.exists())
		{
			throw new RuntimeException("Create Temp File: "+fileName+" Failed!");
		}
		File tempFile=new File(directory.getName()+File.separator+fileName);
		if(tempFile.exists())
		{
			tempFile.delete();
		}
		try
		{
			tempFile.createNewFile();
		} catch (IOException e)
		{
			e.printStackTrace();
		}
		return tempFile;
	}
	
    public boolean genPic(SimpleNode treenode) {
    	if (treenode instanceof ASTFunctionDefinition) {
    		return genPic((ASTFunctionDefinition)treenode);
    	}else if (treenode instanceof ASTNestedFunctionDefinition) {
    		return genPic((ASTNestedFunctionDefinition)treenode);
    	}else if (treenode instanceof ASTTranslationUnit){
    		return genPic((ASTTranslationUnit)treenode);
    	}
    	return false;
    }

    /**
     * @author Liuli 生成调用图
     *2010-4-13
     */
    private boolean genPic(ASTTranslationUnit treenode) {
		CGraph g = treenode.getCGraph();
		String name ="testCallGraph";
		String dot=name+".dot";
		String jpg=name+".jpg";
		File dotFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, dot);
		File jpgFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, jpg);
		
		g.accept(new DumpCGraphVisitor(), dotFile.getPath());
		System.out.println("调用图图输出到了文件" + dotFile.getPath());

		try {
			String cmd="dot -Tjpg -o " + jpgFile.getPath() +" "+ dotFile.getPath();
			Process rt=java.lang.Runtime.getRuntime().exec(cmd);
			
			//zys:防止该进程死等，导致整个程序阻塞
			final InputStream is1 = rt.getInputStream();
			new Thread(new Runnable() {
			    public void run() {
			        BufferedReader br = new BufferedReader(new InputStreamReader(is1));
			        try {
			        	String temp=null;
						while((temp=br.readLine())!= null)
						{
							System.out.println(temp);
						}
					} catch (IOException e) {
					}
			    }
			}).start(); 
			InputStream is2 = rt.getErrorStream();
			BufferedReader br2 = new BufferedReader(new InputStreamReader(is2));
			String line = br2.readLine();
			if (line != null) {
				System.out.println(line);
			} else {
			}
			while((line = br2.readLine()) != null) {
				System.out.println(line);
			}
			rt.waitFor();  
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2){
			e2.printStackTrace();
		}
		System.out.println("调用图打印到了文件" + jpgFile.getPath());
 
		image=jpgFile.getPath();
		return true;
	}
    
    private boolean genPic(ASTNestedFunctionDefinition treenode) {
		Graph g = treenode.getGraph();
		SimpleNode simplejavanode = (SimpleNode) treenode.jjtGetChild(1);
		String name = null;
		if (treenode.getType()!=null) {
			name = treenode.getType().toString();
		} else {
			name = simplejavanode.getImage();
		}
		name = name.replace(' ', '_');
		
		String dot=name+".dot";
		String jpg=name+".jpg";
		File dotFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, dot);
		File jpgFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, jpg);
		
		g.accept(new DumpGraphVisitor(), dotFile.getPath());
		System.out.println("嵌套函数："+treenode.getImage()+"的控制流图输出到了文件" + dotFile.getPath());
		
		try {
			String cmd="dot -Tjpg -o " + jpgFile.getPath() +" "+ dotFile.getPath();
			Process rt=java.lang.Runtime.getRuntime().exec(cmd);
			
			//zys:防止该进程死等，导致整个程序阻塞
			final InputStream is1 = rt.getInputStream();
			new Thread(new Runnable() {
			    public void run() {
			        BufferedReader br = new BufferedReader(new InputStreamReader(is1));
			        try {
			        	String temp=null;
						while((temp=br.readLine())!= null)
						{
							System.out.println(temp);
						}
					} catch (IOException e) {
					}
			    }
			}).start(); 
			InputStream is2 = rt.getErrorStream();
			BufferedReader br2 = new BufferedReader(new InputStreamReader(is2));
			String line = br2.readLine();
			if (line != null) {
				System.out.println(line);
			} else {
			}
			while((line = br2.readLine()) != null) {
				System.out.println(line);
			}
			rt.waitFor();  
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2){
			e2.printStackTrace();
		}
		
		System.out.println("嵌套函数："+treenode.getImage()+"的控制流图打印到了文件" + jpgFile.getPath());
		image=jpgFile.getPath();
		return true;
	}
    
	private boolean genPic(ASTFunctionDefinition treenode) {
		Graph g = treenode.getGraph();
		SimpleNode simplejavanode = (SimpleNode) treenode.jjtGetChild(1);
		String name = null;
		if (treenode.getType()!=null) {
			name = treenode.getType().toString();
		} else {
			name = simplejavanode.getImage();
		}
		name = name.replace(' ', '_');
		name=name.replace('*', 'P');
		String dot=name+".dot";
		String jpg=name+".jpg";
		File dotFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, dot);
		File jpgFile=createTempFile(TestCaseGeneratorForScopeAndDeclarationFinder.TEMPDIR, jpg);
		
		g.accept(new DumpGraphVisitor(), dotFile.getPath());
		System.out.println("函数："+treenode.getImage()+"的控制流图输出到了文件" + dotFile.getPath());
		
		try {
			String cmd="dot -Tjpg -o " + jpgFile.getPath() +" "+ dotFile.getPath();
			Process rt=java.lang.Runtime.getRuntime().exec(cmd);
			
			//zys:防止该进程死等，导致整个程序阻塞
			final InputStream is1 = rt.getInputStream();
			new Thread(new Runnable() {
			    public void run() {
			        BufferedReader br = new BufferedReader(new InputStreamReader(is1));
			        try {
			        	String temp=null;
						while((temp=br.readLine())!= null)
						{
							System.out.println(temp);
						}
					} catch (IOException e) {
					}
			    }
			}).start(); 
			InputStream is2 = rt.getErrorStream();
			BufferedReader br2 = new BufferedReader(new InputStreamReader(is2));
			String line = br2.readLine();
			if (line != null) {
				System.out.println(line);
			} else {
			}
			while((line = br2.readLine()) != null) {
				System.out.println(line);
			}
			rt.waitFor();  
		} catch (IOException e1) {
			System.out.println(e1);
		} catch (InterruptedException e2){
			e2.printStackTrace();
		}
		
		System.out.println("函数："+treenode.getImage()+"的控制流图打印到了文件" + jpgFile.getPath());
		image=jpgFile.getPath();
		return true;
	}
	
	/**
	 * appends the given fragment to the XPath expression
	 * 
	 * @param pathFragment
	 *            fragment to be added
	 * @param appender
	 *            object that is trying to append the fragment
	 */
	public void appendToXPathExpression(String pathFragment, Object appender)
	{
		fireViewerModelEvent(new ViewerModelEvent(appender, ViewerModelEvent.PATH_EXPRESSION_APPENDED, pathFragment));
	}

	public void addViewerModelListener(ViewerModelListener l)
	{
		listeners.add(l);
	}

	public void removeViewerModelListener(ViewerModelListener l)
	{
		listeners.remove(l);
	}

	public void fireViewerModelEvent(ViewerModelEvent e)
	{
		String test = null;
		String path = "softtest.tools.c.viewer.gui.ImagePanel";
		for (int i = 0; i < listeners.size(); i++)
		{		
			test = listeners.get(i).getClass().getName().toString();
			if(test == path){
				if(e.getReason() == ViewerModelEvent.IMAGE_REPAINT){
					((ViewerModelListener) listeners.get(6)).viewerModelChanged(e);
					continue;
				}
				if(e.getReason() == ViewerModelEvent.IMAGE_CG_REPAINT){
					((ViewerModelListener) listeners.get(7)).viewerModelChanged(e);
					continue;
				}
			}else{			
				((ViewerModelListener) listeners.get(i)).viewerModelChanged(e);
			}		
		}
	}
}
