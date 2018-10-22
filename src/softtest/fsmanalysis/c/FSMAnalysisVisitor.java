package softtest.fsmanalysis.c;

import softtest.ast.c.*;
import softtest.rules.c.AliasSet;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.database.c.DBAccess;
import softtest.dscvp.c.GenerateDSCVP;
import softtest.fsm.c.*;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;
import java.util.concurrent.CopyOnWriteArraySet;

import org.apache.log4j.Logger;

public class FSMAnalysisVisitor extends CParserVisitorAdapter {
	/** 待分析状态机集合 */
	private static List<FSMMachine> fsms = new LinkedList<FSMMachine>();
	private static List<FSMMachine> fileScopeFsms = new LinkedList<FSMMachine>();
	
	/** 迭代次数控制 */
	public static int LOOP_NUM = 1;
	
	private FSMControlFlowData loopdata;
	
	private static CopyOnWriteArraySet<Report> reports;	
	//private static Set<Report> reports;
	
	private static CopyOnWriteArraySet<Report> all_reports;	
	//private static Set<Report> all_reports;
	
	public FSMAnalysisVisitor(FSMControlFlowData loopdata) {
		this.loopdata = loopdata;
		reports=new CopyOnWriteArraySet<Report>();
		//reports = new LinkedHashSet<Report>();
		all_reports=new CopyOnWriteArraySet<Report>();
		//all_reports = new LinkedHashSet<Report>();
	}
	
	/** 增加fsm到状态机集合 */
	public static void addFSMS(FSMMachine fsm) {
		if (fsm.getScope() != FSMScope.METHOD) {
			fileScopeFsms.add(fsm);
		} else {
			fsms.add(fsm);
		}
	}
	
	public static List<FSMMachine> getFSMs() {
		return fsms;
	}
	
	public static void clearFSMS(){
		fsms.clear();
		fileScopeFsms.clear();
	}
	
	private static Logger logger = Logger.getLogger(FSMAnalysisVisitor.class);

	/**
	 * 添加对当前文件故障的检测，原先的故障模式只能局限检测当前函数内的故障
	 */
	@Override
	public Object visit(ASTTranslationUnit treenode, Object data) {
		reports.clear();
		all_reports.clear();
		Iterator<FSMMachine> i = fileScopeFsms.iterator();
		while (i.hasNext() && !Thread.currentThread().isInterrupted()) {
			FSMMachine fsm = i.next();
			List<FSMMachineInstance> list = null;
			try {
				Object[] args = new Object[2];
				args[0] = treenode;
				args[1] = fsm;
				list = (List<FSMMachineInstance>) fsm.getRelatedMethod().invoke(null, args);
			} catch (Exception e) {
				logger.error("Can't create "+fsm.getName()+" FSM instances.", e);
			}
			if (list == null || list.size()==0) {
				continue;
			}
			// 由于文件或者全局作用域中的并不跟具体的某个控制流节点对应，因此状态机检测只能针对抽象语法树进行
			for (FSMMachineInstance o : list) {
				runStateMachine(o, treenode, loopdata);
				if(Config.FSM_STATISTIC){
					if(FSMMachine.statistic.get(o.getFSMMachine().getName())!=null){
						Integer count=FSMMachine.statistic.get(o.getFSMMachine().getName());
						count--;
						if(count==0){
							FSMMachine.statistic.remove(o.getFSMMachine().getName());
						}else{
							FSMMachine.statistic.put(o.getFSMMachine().getName(), count);
						}
					}
				}
			}
			list.clear();
		}
		if (!Config.REGRESS_RULE_TEST && !Config.ISTRIAL) {
			for (Report report : reports) {
				loopdata.getDB().exportErrorData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo(), report.getDSCVP());
				// add by cmershen,2016.3.3
				System.out.println(report.getRelatedVarName());
			}
			for(Report report : all_reports){
				loopdata.getDB().exportComplementData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo());
				System.out.println(report.getRelatedVarName());
			}
		} else {
			for (Report report : reports) {
				loopdata.addReport(report);
			}
			for (Report report : all_reports) {
				loopdata.addAllReport(report);
			}
		}
		loopdata.errorNum += reports.size();
		return super.visit(treenode, data);
	}

	/**
	 * 根据状态机类型，路径相关或者路径无关的，遍历控制流图节点
	 * @param g
	 * @param treenode
	 */
	private void visitFunction(Graph g, ASTFunctionDefinition treenode) {
		reports.clear();
		all_reports.clear();
		Iterator<FSMMachine> i = fsms.iterator();
		if (treenode.getEndLine() > loopdata.srcFileLine) {
			loopdata.srcFileLine = treenode.getEndLine();
		} 
		List<FSMMachineInstance> list = null;
		while (i.hasNext() && !Thread.currentThread().isInterrupted()) {
			FSMMachine fsm = i.next();
			//List<FSMMachineInstance> list = null;
			try {
				Object[] args = new Object[2];
				args[0] = treenode;
				args[1] = fsm;
				list = (List<FSMMachineInstance>) fsm.getRelatedMethod().invoke(null, args);
			} catch (Exception e) {
				logger.error("Can't create "+fsm.getName()+" FSM instances.", e);
			}
			if (list == null || list.size()==0) {
				continue;
			}
			if (fsm.isPathSensitive()) {
				treenode.getVexlist().get(0).getFSMMachineInstanceSet().addFSMMachineInstances(list);
			} else {
				for (FSMMachineInstance o : list) {
					//zys:2010.4.25 是不是在此处就把非路径敏感的IP找出来了？同样不依赖于控制流图？
					runStateMachine(o, treenode.getVexlist().get(0), loopdata);
					if(Config.FSM_STATISTIC){
						if(FSMMachine.statistic.get(o.getFSMMachine().getName())!=null){
							Integer count=FSMMachine.statistic.get(o.getFSMMachine().getName());
							count--;
							if(count == 0){
								FSMMachine.statistic.remove(o.getFSMMachine().getName());
							}else{
								FSMMachine.statistic.put(o.getFSMMachine().getName(), count);
							}
						}
					}
				}
				list.clear();
			}
		}
		//zys:2010.8.3	如果函数头结点没有关联自动机，则不对该函数进行状态机计算
		int j=0;
		if (treenode.getVexlist().get(0).getFSMMachineInstanceSet().getTable().size()!=0) {
			if (j == LOOP_NUM - 1) {
				loopdata.reporterror = true;
			} else {
				loopdata.reporterror = false;
			}
				
			if(Config.PATH_SENSITIVE==0 || g.getVexNum()>Config.MAXVEXNODENUM){
				int old = Config.PATH_SENSITIVE;
				Config.PATH_SENSITIVE = 0;
				g.numberOrderVisit(new FSMPathInsensitiveVisitor(), loopdata);
				Config.PATH_SENSITIVE = old;
			}
			else if(Config.PATH_SENSITIVE==2 && g.getPathcount() >0 && g.getPathcount() < Config.PATH_LIMIT){
				g.numberOrderVisit(new FSMControlFlowVisitor(), loopdata);
			}
			else {
				// 把全路径敏感转换为状态合并
				int old = Config.PATH_SENSITIVE;
				Config.PATH_SENSITIVE = 1;
				g.numberOrderVisit(new FSMControlFlowVisitor(), loopdata);
				Config.PATH_SENSITIVE = old;
				//added by liuyan 2015/10/29
//				logger.info("如果执行到这里，为全路径敏感，状态合并过！");
			}
			g.clearVisited();
		}
		if (!Config.REGRESS_RULE_TEST && !Config.ISTRIAL) {
			for (Report report : reports) {
				loopdata.getDB().exportErrorData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo(),report.getDSCVP());
			}
			//added by xwt
			for(Report report : all_reports){
				loopdata.getDB().exportComplementData(report.getIPMethod(),report.getEclass(), report.getFsmName(), report.getFileName(), report.getRelatedVarName(),
						report.getBeginLine(), report.getErrorLine(), report.getDesp(),
						report.getSrcCode(), report.getPreCond(), report.getTraceInfo());
			}
		} else {
			for (Report report : reports) {
				loopdata.addReport(report);
			}
			//added by xwt
			for (Report report : all_reports) {
				loopdata.addAllReport(report);
			}
		}
		loopdata.errorNum += reports.size();
	}
	
	@Override
	public Object visit(ASTFunctionDefinition treenode, Object data) {
		Graph g = treenode.getGraph();
		if (g != null) {
			if(Config.FSM_STATISTIC)
				logger.info("模式计算，开始处理函数："+treenode.getDecl().getImage());
			visitFunction(g, treenode);
			g.clear();
		}
		return null;
	}
	
	/**
	 * 运行故障状态机检测当前函数中的故障，故障为路径不敏感
	 * @param fsminstance
	 * @param n
	 * @param loopdata
	 */
	private void runStateMachine(FSMMachineInstance fsminstance, VexNode n, FSMControlFlowData loopdata)
	{
		boolean stateschanged = false;
		do
		{
			stateschanged = false;
			FSMStateInstanceSet newstates = new FSMStateInstanceSet();
			// 遍历当前状态机实例的所有状态实例
			Iterator<FSMStateInstance> is = fsminstance.getStates().getTable().values().iterator();
			while (is.hasNext())
			{
				FSMStateInstance stateinstance = is.next();
				FSMState state = stateinstance.getState();
				Hashtable<String, FSMTransition> trans = state.getOutTransitions();
				// 计算当前状态实例的所有可能状态转换
				boolean b = false;
				for (Enumeration<FSMTransition> e = trans.elements(); e.hasMoreElements();)
				{
					FSMTransition transition = e.nextElement();
					if (transition.evaluate(fsminstance, stateinstance, n))
					{
						// 需要状态转换
						if (transition.getToState().isError())
						{
							dumpError(fsminstance, n);
							if (loopdata != null) {
								errorReport(loopdata, fsminstance, n,false);
								fsminstance.setErrorReport(true);
							}					
						}
						//added by xwt
						else if(transition.getToState().isFinal() ){
							if(Config.TRIAL_OUTPUT_ALL && !fsminstance.isErrorReport()){
								errorReport(loopdata, fsminstance, n, true);
							}
						}
						FSMStateInstance newstateinstance = new FSMStateInstance(transition.getToState());
						newstateinstance.setSiteNode(n);
						newstates.addStateInstanceWithoutConditon(newstateinstance);
						b = true;
						stateschanged = true;
					}
				}
				if (!b) {
					// 状态没有变化
					newstates.addStateInstanceWithoutConditon(stateinstance);
				}
			}
			fsminstance.setStates(newstates);
		} while (stateschanged);
	}
	
	/**
	 * 运行当前文件或者工程内的故障检测机，检测范围不针对某个函数，因此不能针对控制流节点编写状态机
	 * 
	 * @param fsminstance
	 * @param treenode
	 * @param loopdata
	 */
	private void runStateMachine(FSMMachineInstance fsminstance, SimpleNode treenode, FSMControlFlowData loopdata)
	{
		boolean stateschanged = false;
		do
		{
			stateschanged = false;
			FSMStateInstanceSet newstates = new FSMStateInstanceSet();
			// 遍历当前状态机实例的所有状态实例
			Iterator<FSMStateInstance> is = fsminstance.getStates().getTable().values().iterator();
			while (is.hasNext())
			{
				FSMStateInstance stateinstance = is.next();
				FSMState state = stateinstance.getState();
				Hashtable<String, FSMTransition> trans = state.getOutTransitions();
				// 计算当前状态实例的所有可能状态转换
				boolean b = false;
				for (Enumeration<FSMTransition> e = trans.elements(); e.hasMoreElements();)
				{
					FSMTransition transition = e.nextElement();
					if (transition.evaluate(fsminstance, stateinstance, treenode))
					{
						// 需要状态转换
						if (transition.getToState().isError())
						{
							dumpError(fsminstance, null, treenode);
							if (loopdata != null) {
								errorReport(loopdata, fsminstance, null, treenode,false);
								fsminstance.setErrorReport(true);
							}
						}
						//added by xwt
						else if(transition.getToState().isFinal() ){
							if(Config.TRIAL_OUTPUT_ALL && !fsminstance.isErrorReport()){
								errorReport(loopdata, fsminstance, null, treenode, true);
							}
						}
						FSMStateInstance newstateinstance = new FSMStateInstance(transition.getToState());
						newstates.addStateInstanceWithoutConditon(newstateinstance);
						b = true;
						stateschanged = true;
					}
				}
				if (!b) {
					// 状态没有变化
					newstates.addStateInstanceWithoutConditon(stateinstance);
				}
			}
			fsminstance.setStates(newstates);
		} while (stateschanged);
	}
	
	/**
	 * 在控制台输出检测出来的错误
	 * @param fsminstance
	 * @param n
	 */
	private void dumpError(FSMMachineInstance fsminstance, VexNode n) {
		dumpError(fsminstance, n, null);
	}
	
	public static int count = 1;
	public static void dumpError(FSMMachineInstance fsminstance, VexNode n, SimpleNode node) {
		String str = "发现第["+count+"]个故障" + fsminstance.getFSMMachine().getName() + "，故障行";
		int line = 0;
		if (fsminstance.getNodeUseToFindPosition()!=null) {
			line = fsminstance.getNodeUseToFindPosition().getEndLine();
		} else  if (fsminstance.getRelatedASTNode() != null) {
			line = fsminstance.getRelatedASTNode().getBeginLine();
		} else {
			if (n != null) {
				line = n.getTreenode().getEndLine();
			} else if (node != null) {
				line = node.getBeginLine();
			}
		}
		str += line+"行";

		if (fsminstance.getFSMMachine().isVariableRelated()) {
			VariableNameDeclaration varDecl = fsminstance.getRelatedVariable();
			if (varDecl != null) {
				str = str + "，变量" + fsminstance.getRelatedVariable().getImage();
				if (varDecl.getNode() != null) {
					str = str + "在 " + varDecl.getNode().getBeginLine()+"行声明"+"\n";
//				        + ", 文件位置: "+ varDecl.getFileName();
				}
			} else {
				str += ", " + fsminstance.getResultString();
			}
			
		} else if (fsminstance.getRelatedObject() != null
				&& fsminstance.getRelatedObject().getTagTreeNode() != null) {
			str = str + ",变量 "
					+ fsminstance.getResultString()
					+ "在"
					+ fsminstance.getRelatedObject().getTagTreeNode().getBeginLine()+"行声明.";										
//			str += " in file: " + fsminstance.getRelatedObject().getTagTreeNode().getFileName();
		} else if(fsminstance.getRelatedASTNode()!=null){
			str = str + ",变量"
					  + fsminstance.getResultString() +"\n"
					  + "所在行" +fsminstance.getRelatedASTNode().getBeginLine();
//					  + ", column:" + fsminstance.getRelatedASTNode().getBeginColumn();										              
//			str += "; in file: " + fsminstance.getRelatedASTNode().getFileName();
		}else{
			str = str + ",相关变量" + fsminstance.getResultString();
		}
		if (fsminstance.getTraceinfo().length() > 1) {
			str += " \n" + fsminstance.getTraceinfo();
		}
		if(!Config.SKIP_METHODANALYSIS){
			if (Config.FSMInstanceAnalysis) {
				logger.info(str);
				++count;
			}
		}
	}

	public static void errorReport(FSMControlFlowData loopdata, FSMMachineInstance fsminstance, VexNode n, boolean isAllReport) {
		errorReport(loopdata, fsminstance, n, null,isAllReport);
	}
	
	public static void errorReport(FSMControlFlowData loopdata, FSMMachineInstance fsminstance, VexNode n, SimpleNode node,boolean isAllReport) {
		//ytang add 20161016
		String dscvp = "";
		if(Config.Cluster) {
			GenerateDSCVP.getIPLocation(loopdata, fsminstance, n, node, false);
			dscvp = GenerateDSCVP.start();
		}
		SimpleNode treenode = fsminstance.getRelatedASTNode();	
		int beginline = 0;
		int errorline = 0;
		int errorColumn = 0;
		String variable = "";
		if(fsminstance.getNodeUseToFindPosition()!=null){
			errorline=fsminstance.getNodeUseToFindPosition().getEndLine();
		}else if(fsminstance.getFSMMachine().isPathSensitive()){
			if (n != null) {
				if(fsminstance.getFSMMachine().isVariableRelated() && !fsminstance.getFSMMachine().getName().startsWith("MLF")){
					String name = n.getName();
					if (name.startsWith("func_out") || name.startsWith("if_out")) {
						errorline = n.getTreenode().getEndLine();
						errorColumn = n.getTreenode().getEndColumn();
					} else {
						errorline = n.getTreenode().getBeginLine();
						errorColumn = n.getTreenode().getBeginColumn();
					}
				}else if (!n.isBackNode())
				{
					errorline = n.getTreenode().getBeginLine();
					errorColumn = n.getTreenode().getBeginColumn();
				}else{   
					errorline = n.getTreenode().getEndLine();
					errorColumn = n.getTreenode().getEndColumn();
				}
			} else if (node != null){
				errorline = fsminstance.getRelatedASTNode().getBeginLine();
				errorColumn = fsminstance.getRelatedASTNode().getBeginColumn();
			}
		}else if(treenode != null){
			errorline = treenode.getBeginLine();
			errorColumn = treenode.getBeginColumn();
		}else if(fsminstance.getRelatedObject()!=null && fsminstance.getRelatedObject().getTagTreeNode()!=null){
			errorline=fsminstance.getRelatedObject().getTagTreeNode().getBeginLine();
			errorColumn=fsminstance.getRelatedObject().getTagTreeNode().getBeginColumn();
		}
		
		if (fsminstance.getFSMMachine().isVariableRelated() && fsminstance.getRelatedVariable() != null)
		{
			if (fsminstance.getRelatedVariable().getNode() != null) {
				beginline = fsminstance.getRelatedVariable().getNode().getBeginLine();
			}
			variable = fsminstance.getRelatedVariable().getImage();
			if (!fsminstance.getResultString().equals(variable)) {
				variable = fsminstance.getResultString();
			}
			if (beginline == 0 && fsminstance.getStateData() != null && fsminstance.getFSMMachine().getName().equals("OOB")) {
				beginline = (Integer)fsminstance.getStateData();
			}
		}
		else 
		{
			if(treenode != null)
			{
				beginline = treenode.getBeginLine();
			}
			//zhangguannan
			else if(fsminstance.getRelatedObject() instanceof AliasSet)
			{
				beginline = fsminstance.getRelatedObject().getTagTreeNode().getBeginLine();
			}
			else if(fsminstance.getRelatedObject()!=null && fsminstance.getRelatedObject().getTagTreeNode()!=null){
				beginline=fsminstance.getRelatedObject().getTagTreeNode().getBeginLine();	
			}
			variable = fsminstance.getResultString();
		}
		FSMMachine fsm = fsminstance.getFSMMachine();
		String fileName = loopdata.getCurFileName();
		if (fsminstance.getRelatedASTNode() != null) {
			//fileName = fsminstance.getRelatedASTNode().getFileName();
			if(Config.GCC_TYPE == 0 || Config.GCC_TYPE == 1){
				if (fileName==null || !fileName.contains("\\") ) {
					fileName = loopdata.getCurFileName();
				}
				
			}else{
				if (fileName==null || !fileName.contains(":\\") ) {
					fileName = loopdata.getCurFileName();
				}
			}		
		}
		//dongyk 20121031 解决 测试文件路径中文乱码
		try
		{
			fileName=new String(fileName.getBytes("gbk"), "GB2312"); 
		}catch(Exception e)
		{}
	/*	dongyk 20120614 处理上交所的源文件的路径
		if(fileName!=null && fileName.contains("[") &&fileName.contains("]")&& fileName.contains(";"))
		{
			fileName=fileName.substring(0, fileName.lastIndexOf("."));			
			fileName=fileName.replace('[', '\\');
			fileName=fileName.replace(']', '\\');
			fileName=fileName.replace('.', '\\');
			fileName=fileName+".C";
		}
	*/	
		//U9$:[LLIU.PROD.SRC]SHOWRB.C;5     U9$:[LLIU.PROD.SRC]SHOWRB.C;5
		//U9$:\LLIU\PROD\SRC\SHOWRB.C
		String preconditions = getPrecontions(loopdata.getCurFileName(),treenode);
		String desp = fsminstance.getDesp();
		
			Report report = new Report(fsminstance.getFSMMachine().getName(), fileName ,variable,beginline,errorline);
			//zh 2013-05-13 add method to the database
			String MethodName = "";
			SimpleNode relatedNode = fsminstance.getRelatedASTNode();
			ASTFunctionDefinition defNode = null;
			ASTDeclarator decNode=null;
			ASTDirectDeclarator directDecNode = null;
			if(relatedNode != null){
				if(relatedNode.getFirstParentOfType(ASTFunctionDefinition.class) != null ){
					defNode =(ASTFunctionDefinition) relatedNode.getFirstParentOfType(ASTFunctionDefinition.class);
					if(defNode!=null && defNode.jjtGetNumChildren()>2 )
					{
						decNode = (ASTDeclarator)defNode.getFirstDirectChildOfType(ASTDeclarator.class);  
						if(decNode!=null)
						{
							directDecNode =(ASTDirectDeclarator) decNode.getFirstDirectChildOfType(ASTDirectDeclarator.class); 
							if((directDecNode!=null) && (directDecNode.isFunctionName()== true))
								MethodName = directDecNode.getImage();
							}
						}
					}	
				
				}
			
			report.setIPMethod(MethodName);	
			report.setEclass(fsm.getType());
			report.setDesp(desp);
			report.setPreCond(preconditions);
			report.setErrorColumn(errorColumn);
			report.setTraceInfo(fsminstance.getTraceinfo());
			report.setSrcCode(DBAccess.getSouceCode(fileName, errorline, errorline));
			//ytang add 20161021
			if(Config.Cluster)
				report.setDSCVP(dscvp);	
			//added by cmershen,2016.3.3
			//System.out.println(report.getRelatedVarName());
//			ArrayList<NameOccurrence> occurrenceList = n.getOccurrences();
//			for(NameOccurrence occurrence : occurrenceList) {
//				if(occurrence.getImage().equals(report.getRelatedVarName())) {
//					if(occurrence.getOccurrenceType() == OccurrenceType.USE || occurrence.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE) {
//						List<NameOccurrence> DefUseList = occurrence.getUse_def();
//						printDef(DefUseList,report.getFileName());
//					}
//					else { // 该IP点就是定义点
//						List<NameOccurrence> UndefDefList = occurrence.getUndef_def();
//						printDef(UndefDefList,report.getFileName());
//					}
//				}
//				else if(report.getFsmName().startsWith("OOB")) { // 数组越界错误要考虑下标的定义点
//					if(!occurrence.getImage().equals(report.getRelatedVarName())) {
//						List<NameOccurrence> DefUseList = occurrence.getUse_def();
//						printDef(DefUseList,report.getFileName());
//					}
//				}
//			}

//			logger.info("IP Classification = "+report.getFsmName());
//			logger.info("Related variable = "+report.getRelatedVarName());
//			logger.info("IP所在的控制流图节点是："+n.toString());
//			SimpleNode definition = getDefinitionNodes(report, fsminstance, n, node);
//			if(definition!=null)
//				logger.info("Definition Point = "+definition+",start line = " + definition.getBeginLine() + ",end line = " + definition.getEndLine());
//			else
//				logger.error("Definition Point not found!!!");

		if(isAllReport == false){
			reports.add(report);
		}
		else if(isAllReport == true){
			all_reports.add(report);
		}
		
		//loopdata.getDB().exportErrorData(fsm.getType(), fsm.getName(), fileName, variable,beginline,errorline, desp,
		//		DBAccess.getSouceCode(fileName, errorline, errorline),preconditions, fsminstance.getTraceinfo());
	}
	//added by cmershen,2016.3.21
	/**
	 * 
	 * @param report
	 * @param fsminstance
	 * @param n
	 * @param node
	 * @return
	 * 输入一个IP点，返回对应定义点（抽象语法树节点）
	 */
	private static SimpleNode getDefinitionNodes(Report report, FSMMachineInstance fsminstance, VexNode n, SimpleNode node) {
		String ipImage = report.getRelatedVarName();
		if(report.getRelatedVarName()==null || report.getRelatedVarName().equals(""))
			ipImage = fsminstance.getVarImage();	
		if(ipImage.contains(".")) {
			System.out.println("故障点出现在结构体的成员部分，修正故障点！");
			String[] temp = ipImage.split("\\.");
			ipImage = temp[temp.length-1];
			System.out.println("新的故障点变量为:"+ipImage);
		}
		if(report.getFsmName().startsWith("MLF") || report.getFsmName().startsWith("RL")) {
		//if(n.toString().startsWith("func_out")) {
			boolean getIPNode = false;
			Queue<VexNode> queue = new LinkedList<VexNode>();
			queue.offer(n);
			while(!getIPNode) {
				VexNode temp = queue.poll();
				if(temp==null || getIPNode)
					break;
				for(NameOccurrence occ : temp.getOccurrences()) {
					if(occ.getImage().equals(ipImage)) {
						n=temp;
						getIPNode=true;
						break;
					}
				}
				queue.addAll(getParentNodes(temp));
//				for(VexNode parentNode: getParentNodes(n)) {
//					for(NameOccurrence occ : parentNode.getOccurrences()) {
//						if(occ.getImage().equals(ipImage)) {
//							n=parentNode;
//							getIPNode=true;
//							break;
//						}
//					}
//				}				
				
				if(n.toString().startsWith("func_head"))
					break;
			}
		}
		for(NameOccurrence occ : n.getOccurrences()) {
			if(occ.getImage().equals(ipImage)) {
				if(occ.getUse_def()!=null && occ.getUse_def().size()>0) {
					for(NameOccurrence usedef : occ.getUse_def()) {
						return usedef.getLocation();
					}
				}
				else if(occ.getUndef_def()!=null && occ.getUndef_def().size()>0) {
					for(NameOccurrence undefdef : occ.getUndef_def()) {
						return undefdef.getLocation();
					}
				}
				else if(occ.getOccurrenceType()==OccurrenceType.DEF)
					return n.getTreenode();
			}
		}
		
		
		return null;
	}
	private static VexNode getChild(VexNode temp, String domain) {
		Hashtable<String, Edge> outedges = temp.getOutedges();
		for(Edge edge:outedges.values()) {
			VexNode child = edge.getHeadNode();
			if(child.getValueSet().getTable().values().contains(domain))
				return child;
		}
		return null;
	}
	private static List<VexNode> getParentNodes(VexNode n) {
		List<VexNode> parentNodes = new ArrayList<VexNode>();
		Hashtable<String, Edge> inedges = n.getInedges();
		for(Edge edge:inedges.values()) {
			parentNodes.add(edge.getTailNode());
		}
		return parentNodes;
	}
	//added by cmershen,2016.3.3
	private static void readLineOfFile(String fileName, int lineNumber) throws IOException {
		BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream(fileName))); 
		String line = reader.readLine(); 
		int num = 0; 
		while (line != null) { 
			if (lineNumber == ++num) { 
				System.out.println("line " + lineNumber + ": " + line); 
			} 
			line = reader.readLine(); 
		} 
		reader.close(); 
	} 
	@SuppressWarnings("unused")
	private static void printDef(List<NameOccurrence> list,String fileName) {
		if(list!=null && list.size()>0) {
			NameOccurrence defPoint = list.get(list.size()-1);
			SimpleNode tempNode = defPoint.getDeclaration().getNode(); // 找到定义点，向上找到Statement节点
			while (!(tempNode instanceof ASTStatement)) {
				tempNode=(SimpleNode) tempNode.jjtGetParent();
			}	
			boolean isAssign = false;
			boolean isIteration = false;

			if(tempNode.containsChildOfType(ASTAssignmentExpression.class))
				isAssign = true;
			if(tempNode.containsChildOfType(ASTIterationStatement.class)) {			
				isAssign = false;
				isIteration = true;
			}
			if(isAssign) { //存在定制方法1-赋值语句
				System.out.println("本IP的定义点属于：定值方法1-赋值语句,定义点位于第"+tempNode.getBeginLine()+"~"+tempNode.getEndLine()+"行。");
				printLines(fileName,tempNode.getBeginLine(),tempNode.getEndLine());
			}
			else if(isIteration) {
				System.out.println("本IP的定义点属于：定值方法3-循环语句,定义点位于第"+tempNode.getBeginLine()+"~"+tempNode.getEndLine()+"行。");
				printLines(fileName,tempNode.getBeginLine(),tempNode.getEndLine());
			}
		}
	}
	private static void printLines(String fileName,int startLine,int endLine) {
		for(int i = startLine;i<=endLine;i++) {
			try {
				readLineOfFile(fileName,i);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	public static String getPrecontions(String parsefilename, SimpleNode treenode){
		if (treenode == null) {
			return "";
		}
		Node entrynode=treenode.getFirstChildOfType(ASTFunctionDefinition.class);
		Graph g=null;
		VexNode fromvex=null,tovex=treenode.getCurrentVexNode();
		if (entrynode instanceof ASTFunctionDefinition) {
			ASTFunctionDefinition m = (ASTFunctionDefinition)entrynode;
			g = m.getGraph();
			fromvex = m.getCurrentVexNode();
		} 
		if (g!=null && fromvex!=null && tovex!=null) {
			List<VexNode> list = Graph.findAPath(fromvex, tovex);
			StringBuffer buffer=new StringBuffer();
			if(list.size()<2){
				return "";
			}
			ArrayList<Edge> elist=new ArrayList<Edge> ();
			VexNode vex=list.get(0),next;
			for(int i=1;i<list.size();i++){
				next=list.get(i);
				Edge e=vex.getEdgeByHead(next);
				if(e==null){
					return "";
				}
				elist.add(e);
				vex=next;	
			}
			
			for (Edge e:elist) {
				if(e.getName().startsWith("T_")){
					VexNode tailNode = e.getTailNode();
					SimpleNode node = tailNode.getTreenode();
					if(tailNode.getName().startsWith("if_head")) {
						node=(SimpleNode)node.jjtGetChild(0);
						buffer.append(" "+node.getBeginLine()+": ("+DBAccess.getSouceCode(parsefilename, node.getBeginLine(), node.getBeginColumn(), node.getEndLine(), node.getEndColumn())+")==true\r\n");
					} else if(tailNode.getName().startsWith("while_head") || tailNode.getName().startsWith("do_while_out1")){
						node=(SimpleNode)node.jjtGetChild(0);
						buffer.append(" "+node.getBeginLine()+": ("+DBAccess.getSouceCode(parsefilename, node.getBeginLine(), node.getBeginColumn(), node.getEndLine(), node.getEndColumn())+")==true\r\n");
					}
				}else if (e.getName().startsWith("F_")) {
					VexNode tailNode = e.getTailNode();
					SimpleNode node = tailNode.getTreenode();
					if(tailNode.getName().startsWith("if_head")){
						node=(SimpleNode)node.jjtGetChild(0);
						buffer.append(" "+node.getBeginLine()+": ("+DBAccess.getSouceCode(parsefilename, node.getBeginLine(), node.getBeginColumn(), node.getEndLine(), node.getEndColumn())+")==false\r\n");
					} else if(tailNode.getName().startsWith("while_head") || tailNode.getName().startsWith("do_while_out1")){
						node=(SimpleNode)node.jjtGetChild(0);
						buffer.append(" "+node.getBeginLine()+": ("+DBAccess.getSouceCode(parsefilename, node.getBeginLine(), node.getBeginColumn(), node.getEndLine(), node.getEndColumn())+")==false\r\n");
					}
				}
			}
			return buffer.toString();
		}
		return "";
	}
}
