package softtest.rules.keilc.fault;

import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.VexNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;

/**
 * 检测是否有不可达分支
 * @author zys	
 * 2010-4-13
 */
public class URBStateMachine {
	
	public static List<FSMMachineInstance> createURBStateMachines(SimpleNode node, FSMMachine fsm) 
	{
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		if(node instanceof ASTFunctionDefinition)
		{
			Graph g=((ASTFunctionDefinition)node).getGraph();
			Hashtable<String, Edge> nodesTable=g.edges;
	out:	for(Edge edge:nodesTable.values())
			{
				if(edge.getContradict() && 
						(edge.getName().startsWith("T") || edge.getName().startsWith("F")))
				{
					//zys:2010.4.23 对一条不可达分支只上报一次
					//查找当前矛盾边的上一条边，如果上条边也矛盾，则本次不再上报（即只在不可达分支的第一条矛盾边中上报）
//					VexNode pre=edge.getTailNode();
//					for(Edge preEdge:pre.getInedges().values())
//					{
//						if(preEdge.getContradict())
//							break out;
//					}
					VexNode temp=edge.getTailNode();
					addFSM(list, temp, fsm);
				}
			}
		}
		return list;
	}
	
	private static void addFSM(List<FSMMachineInstance> list, VexNode vex, FSMMachine fsm) {
		//System.out.println("当前创建第"+(num++)+"个自动机！");
		FSMMachineInstance fsminstance = fsm.creatInstance();
		SimpleNode node=vex.getTreenode();
		fsminstance.setRelatedASTNode(node);
		fsminstance.setReleatedVexNode(vex);
		String vexName=vex.getName();
		if(vexName.startsWith("if")){
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的if存在不可达分支");
		}else if(vexName.startsWith("for")){
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的for循环存在不可达分支");
		}else if(vexName.startsWith("switch")){
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的switch存在不可达分支");
		}else if(vexName.startsWith("while")){
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的while存在不可达分支");
		}else if(vexName.startsWith("do-while")){
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行的do-while存在不可达分支");
		}else{
			fsminstance.setDesp("位于第"+node.getBeginLine()+"行存在不可达分支");
		}
		list.add(fsminstance);
	}
}
