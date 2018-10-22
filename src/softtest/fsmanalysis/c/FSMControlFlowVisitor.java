package softtest.fsmanalysis.c;

import java.util.*;

import org.apache.log4j.Logger;

import softtest.callgraph.c.CVexNode;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.domain.c.symbolic.Expression;
import softtest.ast.c.*;
import softtest.fsm.c.*;
import softtest.symboltable.c.VariableNameDeclaration;

public class FSMControlFlowVisitor implements GraphVisitor {
	static Logger logger = Logger.getLogger(FSMControlFlowVisitor.class);

	public void calculateIN(VexNode n, Object data) {
		List<Edge> list = new ArrayList<Edge>();
		for (Edge e:n.getInedges().values()) {
			list.add(e);
		}
		Collections.sort(list);
		if (n.getSnumber() != 0) {
			n.getFSMMachineInstanceSet().clear();
		}

		// 计算前驱节点的U(in)
		for(Edge edge:list){
			VexNode pre = edge.getTailNode();
			// 判断分支是否矛盾
			if (edge.getContradict()) { 
				continue;
			}
			
			// 如果前驱节没有访问过则跳过
			if (!pre.getVisited()) {
				continue;
			}

			if (edge.getName().startsWith("T")) {
				FSMMachineInstanceSet temp = new FSMMachineInstanceSet(pre.getFSMMachineInstanceSet());
				temp.calCondition(pre, true);
				n.mergeFSMMachineInstances(temp);
			} else if (edge.getName().startsWith("F")) {
				// 处理一次循环:将循环的回边自动机状态也合并进来？
				if (n.getName().startsWith("while_out") || n.getName().startsWith("for_out")) {
					FSMControlFlowData loopdata = (FSMControlFlowData) data;
					loopdata.reporterror = false;
					visit(pre, loopdata);
					loopdata.reporterror = true;
				}
				FSMMachineInstanceSet temp = new FSMMachineInstanceSet(pre.getFSMMachineInstanceSet());
				temp.calCondition(pre, false);
				n.mergeFSMMachineInstances(temp);
			}else if(n.getName().startsWith("label_head_default") || n.getName().startsWith("label_head_case")){
				if(pre.getName().startsWith("switch_head")){
					FSMMachineInstanceSet temp = new FSMMachineInstanceSet(pre.getFSMMachineInstanceSet());
					temp.calSwitch(n, pre);
					n.mergeFSMMachineInstances(temp);
				}
			}else {
				
				n.mergeFSMMachineInstances(pre.getFSMMachineInstanceSet());
			}
		}
	}

	public void calculateOUT(VexNode n, Object data) {
		
		//add by WangQian 2010-10-15  switch中case:/default: 后面跟{}的情况  会有xpath寻路错误的情况
		if(n.getName().indexOf("label")!= -1)
		{
			return;
		}
		
		List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = n.getInedges().elements(); e.hasMoreElements();) {
			list.add(e.nextElement());
		}
		
		Collections.sort(list);
		VexNode pre = null;
		//added by liuyan 2015/11/4
		for(Edge e:list){
			String str = e.getTailNode().toString();
			StringBuffer stringBuffer = new StringBuffer();
			StringBuffer string = new StringBuffer();
			if(str.length() > 11 && str.charAt(2) == 'f'){
				for(int i = 2; i<11;++i){
					stringBuffer.append(str.charAt(i));
				}
				String string2[] = str.split("_");
				for(int j = 2;j<string2.length-1;++j){
					string.append(string2[j]);
					if(j != string2.length-2){
						string.append("_");
					}
				}
			}
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					if(stringBuffer.toString().equals("func_head")){
						logger.info("开始分析函数"+string.toString()+"()…………");
					}
				}
			}
		}
		
		
		SimpleNode treenode = n.getTreenode();
		if(!Config.SKIP_METHODANALYSIS){
			if(Config.FSMInstanceAnalysis){
				logger.info("分析当前的节点名字为["+treenode.getCurrentVexNode().getName()+"]");
				
			}
		}
		
		if (treenode == null)
			return;
		if (!n.isBackNode()) {
			// 重新计算状态条件
			n.getFSMMachineInstanceSet().calDomainSet(n);
		}
		// 计算当前节点的Out
		List<FSMMachineInstance> todelete = new ArrayList<FSMMachineInstance>();
		Set<FSMMachineInstance> fsmSet = n.getFSMMachineInstanceSet().getTable().keySet();
		
		//added by liuyan 2015/10/13
//		int tempCount = fsmSet.size();
//		logger.info("FSMControlFlowVisitor.java++" + "calculateOUT" + "fsmSet的总大小：" + tempCount);
//		logger.info(fsmSet);
		
		// 遍历所有的状态机实例
		int countNum = 1;
		if(!Config.SKIP_METHODANALYSIS){
			if(Config.FSMInstanceAnalysis){
				logger.info("节点["+treenode.getCurrentVexNode().getName()+"]创建的状态机实例数量为："+fsmSet.size());
			}
		}
		
		for (FSMMachineInstance fsminstance : fsmSet) {
			if(!Config.SKIP_METHODANALYSIS){
				if(Config.FSMInstanceAnalysis){
					logger.info("节点["+treenode.getCurrentVexNode().getName()+"]的第["+countNum+"]个状态机状态信息为：");
					++countNum;
					logger.info(fsminstance);
				}
			}
			
			// 创建新的状态实例集合
			// 状态变化只计算一次了，除了处理p=f(p.i);的情况
			boolean recursion = false;
			do {
				recursion = false;
				FSMStateInstanceSet newstates = new FSMStateInstanceSet();
				
				// 遍历当前状态机实例的所有状态实例
				Set<FSMStateInstance> stateSet = fsminstance.getStates().getTable().keySet();
				for (FSMStateInstance stateinstance : stateSet) {
					ValueSet oldValueSet=n.getValueSet();
					SymbolDomainSet oldSymbolDomainSet=n.getSymDomainset();
					n.setSymDomainset(stateinstance.getSymbolDomainSet());
					n.setValueSet(stateinstance.getValueSet());
					FSMState state = stateinstance.getState();
	
					if (state.getRelatedMethod() != null) {
						try {
							Object[] args = new Object[2];
							args[0] = n;
							args[1] = fsminstance;
							state.getRelatedMethod().invoke(null, args);
						} catch (Exception e) {
							logger.error("Can't invoke state method in FSM " + fsminstance.getFSMMachine().getName(), e);
						}
					}
					Hashtable<String, FSMTransition> trans = state.getOutTransitions();
				
					// 计算当前状态实例的所有可能状态转换
					boolean stateschanged = false;
 					for (Enumeration<FSMTransition> e = trans.elements(); e.hasMoreElements();) {
						FSMTransition transition = e.nextElement();
						//检查condition是否需要状态转换
						if (transition.evaluate(fsminstance, stateinstance, n)) {
							// 需要状态转换
							if (transition.getToState().isError()) {
								FSMControlFlowData loopdata = (FSMControlFlowData) data;
								if (loopdata != null && loopdata.reporterror) {
									FSMAnalysisVisitor.dumpError(fsminstance, n, n.getTreenode());
									FSMAnalysisVisitor.errorReport(loopdata, fsminstance, n, false);
									fsminstance.setErrorReport(true);
								}		
								
							}
							//added by xwt	
							else if(transition.getToState().isFinal() ){
								if(Config.TRIAL_OUTPUT_ALL && !fsminstance.isErrorReport()){
									FSMControlFlowData loopdata = (FSMControlFlowData) data;
									FSMAnalysisVisitor.errorReport(loopdata, fsminstance, n, true);
								}
							}
							FSMStateInstance newstateinstance = new FSMStateInstance(transition.getToState());
							newstateinstance.setSymbolDomainSet(stateinstance.getSymbolDomainSet());
							newstateinstance.setValueSet(stateinstance.getValueSet());
							newstateinstance.setSiteNode(n);
							newstates.addStateInstance(newstateinstance);
							stateschanged = true;
							recursion = true;
							
							if(!Config.SKIP_METHODANALYSIS){
								if (Config.FSMInstanceAnalysis) 
								{
									if(Config.StateTransition){
										System.out.println("In Line " + n.getTreenode().getBeginLine() + " " + fsminstance.getResultString()+":"+transition.getName()
												+":"+fsminstance.getStates().toString()+" >> "+newstateinstance.getState().toString());
										System.out.println("VexNode : " + n.getName() + " " +state.getName()+"-->>"+transition.getToState());
										logger.info("节点["+n.getName()+"]的状态机转换过程为:");
										logger.info("在" + n.getTreenode().getBeginLine() + "行变量" + fsminstance.getResultString()+":"+transition.getName()
												+":"+fsminstance.getStates().toString()+" >> "+newstateinstance.getState().toString());
										logger.info("节点[" + n.getName() + "]有状态转换，转换状态为：" +state.getName()+"-->>"+transition.getToState());
									}
							}
							
							}
						}
					}
					if (!stateschanged) {
						// 状态没有变化
						newstates.addStateInstance(stateinstance);
					}
//					if(n.isIP) {
//						System.out.println(n.getName()+" is IP.");
//						for(int i = 0;i<n.reportList.size();i++) {
//							Report report = n.reportList.get(i);
//							FSMMachineInstance fsminstance1 = n.fsmList.get(i);
//							SimpleNode node = n.getTreenode();
//							logger.info("IP Classification = "+report.getFsmName());
//							logger.info("Related variable = "+report.getRelatedVarName());
//							logger.info(getDefinitionNodes(fsminstance1, n, node));
//						}
//					}
					n.setValueSet(oldValueSet);
					n.setSymDomainset(oldSymbolDomainSet);

					if(fsminstance.isErrorReport())
						break;
				}
				fsminstance.setStates(newstates);
				
				if (newstates.isEmpty()) {
					todelete.add(fsminstance);
					break;
				}
				if ((fsminstance.getFSMMachine().getName().startsWith("MLF")&& !fsminstance.getFSMMachine().getName().equals("MLF_LOOP"))
						|| fsminstance.getFSMMachine().getName().equals("RL") 
                        || fsminstance.getFSMMachine().getName().equals("UVF_P")
						|| fsminstance.getFSMMachine().getName().startsWith("UFM")) {
					break;//zys:2010.8.5	为什么？？？	
					//xwt:2011.10.28   当MLF等模式进入分配状态后，在同一个控制流图节点上不允许再进行条件转移判断，否则误报重复申请资源
				}
				//xwt:接下来的if为了一个特殊的模式，虽然很不厚道，但是我想出去啥更好的解决办法了，麻烦啊！
				//原因是：MLF_LOOP原属于MLF类的，直接break就行，但是因为从start转换到loop是在for_head的真分支下一个节点，如果下节点又马上分配内存，这里就不能break了，所以，特殊处理
				if(fsminstance.getFSMMachine().getName().equals("MLF_LOOP")){
					boolean isLoop = true;
					Enumeration<FSMStateInstance> table = fsminstance.getStates().getTable().keys();				
					while (table.hasMoreElements()){
						FSMStateInstance stateInstance = table.nextElement();
						if(stateInstance.getState().getName().equals("Loop"))
							isLoop = false;						
					}
					if(isLoop)
						break;
				}
			} while(recursion);
		}

		// 删除那些空的状态机
		for (FSMMachineInstance it : todelete) {
			n.rmFSMMachineInstanceSet(it);
			if(Config.FSM_STATISTIC){
				String fsmname=it.getFSMMachine().getName();
				Integer count=FSMMachine.statistic.get(fsmname);
				if(count!=null){
					count--;
					try{
					if(count<0){
						throw new RuntimeException(fsmname+" = "+count+" error!");
					}else if(count==0){
						FSMMachine.statistic.remove(fsmname);
					}else{
						FSMMachine.statistic.put(fsmname, count);
					}
					}catch(RuntimeException e){
						e.printStackTrace();
						continue;
					}
				}
			}
		}

		//判断当前节点的前驱节点pre,如果其后继节点都已访问过,则将pre的状态机实例集合清空
		if (Config.FSM_REMOVE_PER_NODE) {
			for(Edge edge : list){
				pre = edge.getTailNode();
//				logger.info("前驱结点pre……"+pre);
				boolean allvisited = true;
				for (Edge tempedge : pre.getOutedges().values()) {
					if (!tempedge.getHeadNode().getVisited()) {
						allvisited = false;
						break;
					}
				}
				if (allvisited && pre.getVisited()) {
					//zys:	2011.9.21	对循环的直接前趋节点进行特殊处理：在循环退出节点需要再次访问循环头节点，此时如果将直接前驱的状态机清空，则会影响
					//后续的迭代计算，导致状态丢失
					if(pre.getOutedges().size()==1){
						VexNode nextNode=pre.getOutedges().elements().nextElement().getHeadNode();
//						logger.info("后置节点迭代中nexeNode……"+nextNode);
						String temp=nextNode.getName();
						if(temp.startsWith("while_head") || temp.startsWith("for_head") 
								|| temp.startsWith("do_while_out1") ){
							//找到循环节点的出口节点，根据其访问标识判断是否可以清空循环前驱节点的状态机实例
							Edge outEdge=null;
							for(Edge out : nextNode.getOutedges().values()){
								if(out.getName().startsWith("F_")){
									outEdge=out;
									break;
								}
							}
							VexNode outNode=outEdge.getHeadNode();
							if(!outNode.getVisited())
								continue;
						}
					}
					pre.clear();//modify by JJL, 2016-11-23, 取消销毁控制流图
				}else{
					//System.out.println("自动机实例集合未清空："+pre.getName());
				}
			}
		}

	}
	private static List<VexNode> getDefinitionNodes(FSMMachineInstance fsminstance, VexNode n, SimpleNode node) {
		List<VexNode> defList = new ArrayList<VexNode>();
		String ipImage = fsminstance.getVarImage();
		Hashtable<VariableNameDeclaration, Expression> valuetable = n.getValueSet().getTable();
		logger.info("Value set of the IP variable is:"+n.getValueSet());
		for(VariableNameDeclaration key:valuetable.keySet()) {
			if(key.getImage().equals(ipImage)) {
				String useDomain = valuetable.get(key).toString();//使用点(IP点)的符号名
				//use BFS to search the first vexnode that doesn't contain "useDomain"
				Queue<VexNode> queue = new LinkedList<VexNode>();
				queue.offer(n);
				while(!queue.isEmpty()) {
					VexNode temp = queue.poll();
					boolean containsDomain = false;
					for(Expression exp : temp.getLastvalueset().getTable().values()) {
						if(exp.toString().equals(useDomain)) {
							containsDomain = true;
							break;
						}							
					}
					if(temp==n)
						containsDomain = true;
					if(!containsDomain) {
						defList.add(temp);
						break;
					}
					for(VexNode parent : getParentNodes(temp)) {
						queue.offer(parent);
					}
				}
			}
		}

		return defList;
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
	/** 对节点进行访问 */
	public void visit(VexNode n, Object data) {
		List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = n.getInedges().elements(); e
				.hasMoreElements();) {
			list.add(e.nextElement());
		}
		//zys: 2011.9.21	循环退出节点的访问标识在逐节点清空状态机时需要特殊判断
		if(!(n.getName().startsWith("while_out") || n.getName().startsWith("for_out")
				|| n.getName().startsWith("do_while_out1")))
			n.setVisited(true);

		if (list.isEmpty()) {
			return;
		}
		calculateIN(n, data);
		
		//zys: 2011.9.21	循环退出节点的访问标识在逐节点清空状态机时需要特殊判断
		if(n.getName().startsWith("while_out") || n.getName().startsWith("for_out")
				|| n.getName().startsWith("do_while_out1"))
			n.setVisited(true);
		
		for(FSMMachineInstance fsmin:n.getFSMMachineInstanceSet().getTable().values())
		{
			if (fsmin.getRelatedObject() != null) {
				fsmin.getRelatedObject().calculateIN(fsmin, n, data);
				fsmin.getRelatedObject().calculateOUT(fsmin, n, data);
			}
		}

		if(!n.getContradict()){
	//		System.out.println(n.getName());
			calculateOUT(n, data);
		}
		
	}

	/** 对边进行访问 */
	public void visit(Edge e, Object data) {

	}

	/** 对图进行访问 */
	public void visit(Graph g, Object data) {

	}
}
