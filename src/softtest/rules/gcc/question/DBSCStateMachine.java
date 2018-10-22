package softtest.rules.gcc.question;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTLabeledStatement;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
/** 
 * @author ssj
 */
public class DBSCStateMachine {

	public static List<FSMMachineInstance> createDBSCStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> switchResults = null;
		List<SimpleNode> ifResults = null;
		//查询所有条件判断和开关语句
		String ifxPath = ".//SelectionStatement[@Image='if']";
		String switchxPath = ".//SelectionStatement[@Image='switch']";
		
		//判断if语句中是否有相同分支/
		ifResults = StateMachineUtils.getEvaluationResults(node, ifxPath);
		Iterator ifitr = ifResults.iterator();
		while(ifitr.hasNext()){
			SimpleNode SelectionStatement = (SimpleNode)ifitr.next();
			if(SelectionStatement.jjtGetNumChildren()!= 3){		//无匹配的else
				continue;
			}else if(!(SelectionStatement.jjtGetChild(1) instanceof ASTStatement )||!(SelectionStatement.jjtGetChild(2) instanceof ASTStatement )){
				continue;
			}else{
				SimpleNode a = (SimpleNode)SelectionStatement.jjtGetChild(1);
				SimpleNode b = (SimpleNode)SelectionStatement.jjtGetChild(2);
				if(!checkEqual(a,b)){
					continue;
				}else{
					addFSM(list,SelectionStatement,fsm);
				}
			}
		}		

		//判断switch语句中是否有相同分支/
		switchResults = StateMachineUtils.getEvaluationResults(node, switchxPath);
		Iterator switchitr = switchResults.iterator();
		while(switchitr.hasNext()){
			SimpleNode SelectionStatement = (SimpleNode)switchitr.next();
			SimpleNode ss = (SimpleNode)SelectionStatement.jjtGetChild(1);
			SimpleNode ASTStatementList = (SimpleNode)ss.getFirstChildOfType(ASTStatementList.class);
			int count = -1;	//case分支数
			if (ASTStatementList == null)
				continue;
			int n = ASTStatementList.jjtGetNumChildren();
			ArrayList<List<SimpleNode>> switchlist = new ArrayList<List<SimpleNode>>();
			SimpleNode sta = null;
			int countnull = 0;//形如：case 1：无任何处理的分支数
			
			//为各分支建表,以排除各种分支结构问题
			for(int i=0;i<n;i++){
				sta = (SimpleNode)ASTStatementList.jjtGetChild(i);
				//处理不以case开头的情况
				if(count < 0 && !(sta.jjtGetChild(0) instanceof ASTLabeledStatement))
					continue;
				if(sta.jjtGetChild(0) instanceof ASTLabeledStatement){
					ASTLabeledStatement labeledStatement = (ASTLabeledStatement)sta.jjtGetChild(0);
//					if(labeledStatement.getFirstChildOfType(ASTLabeledStatement.class) != null){
					if((labeledStatement.jjtGetNumChildren() > 1) && (labeledStatement.jjtGetChild(1).jjtGetChild(0) instanceof ASTLabeledStatement)){
						countnull++;
						labeledStatement = (ASTLabeledStatement)labeledStatement.jjtGetChild(1).jjtGetChild(0);
						if((labeledStatement.jjtGetNumChildren() > 1) && (labeledStatement.jjtGetChild(1).jjtGetChild(0) instanceof ASTLabeledStatement)){
							countnull++;
							break;
//							labeledStatement = (ASTLabeledStatement)labeledStatement.jjtGetChild(1).jjtGetChild(0);
						}else{
							count++;
							sta = (SimpleNode)labeledStatement.getFirstDirectChildOfType(ASTStatement.class);
//							sta = (SimpleNode)labeledStatement.jjtGetChild(1);
							List<SimpleNode> xlist = new ArrayList<SimpleNode>(); 
							xlist.add(sta);
							switchlist.add(count,xlist);
						}
					}else{
						count++;
						sta = (SimpleNode)labeledStatement.getFirstDirectChildOfType(ASTStatement.class);
						List<SimpleNode> xlist = new ArrayList<SimpleNode>(); 
						xlist.add(sta);
						switchlist.add(count,xlist);
					}
				}else{
					switchlist.get(count).add(sta);
				}	
			}
			
			boolean stag = false;
			if(countnull>=2)
				addFSM(list,SelectionStatement,fsm);
			else {
				if(count < 2){
					continue;
				}else{
					for(int i=0;i<=count;i++){
						if (stag) 
						break;
						else{
							for(int j=i+1;j<=count;j++){
								if(checklistequal(i,j,switchlist)){
									stag=true;
									break;
								}
							}
						}
					}
					if(stag)
						addFSM(list,SelectionStatement,fsm);			
				}
			}	
		}
	    return list;
    }
	
	
	/**检查switchlist中的第i个和第j个表是否相同
	 * 即switch语句第i个与j个case分支是否相同*/
	private static boolean checklistequal(int i,int j,ArrayList<List<SimpleNode>> switchlist){
		
		Iterator itr1 = switchlist.get(i).iterator();	
		Iterator itr2 = switchlist.get(j).iterator();	
		
		int num1=0,num2=0;

		while(itr1.hasNext()){
			num1++;
			itr1.next();
		}
		while(itr2.hasNext()){
			num2++;
			itr2.next();
		}
		if(num1!=num2)
		return false;
		else{
			itr1 = switchlist.get(i).iterator();	
			itr2 = switchlist.get(j).iterator();
			
			while(itr1.hasNext()){
				SimpleNode sta1=(SimpleNode)itr1.next();
				SimpleNode sta2=(SimpleNode)itr2.next();
				if(!checkEqual(sta1,sta2))
					return false;	
			}
			return true;
		}	
	}
	
	/**检查a,b节点及所有对应孩子是否相同*/
	private static boolean checkEqual(SimpleNode a,SimpleNode b){
		
		if(!a.toString().equals(b.toString()) || !a.getImage().equals(b.getImage() ) )
			return false;
		String s1 = a.getOperators();
		String s2 = b.getOperators();
		
		/*getOperators()方法返回的值应是null的情况，
		 *实际回值可能是[]或者是“null”.在此将其统一  */
		
		if (s1.equals("[]"))
			s1="null";
		if (s2.equals("[]"))
			s2="null";
		
		if(!s1.equals(s2)){		
			return false;
		}
		if(a.jjtGetNumChildren() != b.jjtGetNumChildren())
			return false;
		if(a.jjtGetNumChildren()==0 && b.jjtGetNumChildren()==0)
			return true;
		for(int i=0;i<a.jjtGetNumChildren();i++){
			if(!checkEqual((SimpleNode)a.jjtGetChild(i),(SimpleNode)b.jjtGetChild(i)))
				return false;
			}
		if(a.getImage().equalsIgnoreCase("goto")){
			if(!a.getImage().equals(b.getImage()))
				return false;
			}
		return true;
	}
		
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" DifferentBranchSameCode: The codes of different branch of selection statement are same.This is an ill conditioned flow control.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("在第"+node.getBeginLine()+"行的条件判断、开关语句的分支是相同的代码: 在条件判断和开关语句的分支中，使用了相同的代码，这是一种病态的控制流。" );
						}	
		list.add(fsminstance);
	
	}
}
