package softtest.rules.gcc.rule;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.VariableNameDeclaration;

/** 
 * @author liruitong
 * fopen函数必须提供打开错误的错误处理机制
 * FMC:Fopen Must Check
 */

public class FMCStateMachine {

	public static List<FSMMachineInstance> createFMCStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = null, evaluationResults1=null,evaluationResults2=null;
		if(!node.getFileName().contains(".h"))
		{
			String xPath=".//Expression[./AssignmentExpression/AssignmentExpression/UnaryExpression/PostfixExpression/PrimaryExpression[@Method='true'][@Image='fopen']]";
			evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
			Iterator itr = evaluationResults.iterator();
			SimpleNode tmpNode=null;  
			boolean isChecked=false;
			while(itr.hasNext()){
				ASTExpression exp = (ASTExpression)itr.next();
				ASTSelectionStatement stm= (ASTSelectionStatement)exp.getFirstParentOfType(ASTSelectionStatement.class);
				ASTPrimaryExpression priExp = (ASTPrimaryExpression)exp.getFirstChildOfType(ASTPrimaryExpression.class);
				if(priExp==null)
					continue;
				if(stm!=null)
				{
					String xPath1="./Expression/AssignmentExpression[@Operators='=']/EqualityExpression[./UnaryExpression/PostfixExpression/PrimaryExpression[@Image='NULL']";
					evaluationResults1 = StateMachineUtils.getEvaluationResults(stm, xPath1);
					if(evaluationResults1.size()!=0)
						{
							isChecked = true;
							continue;
						}
				}
				
				VariableNameDeclaration fileVar=priExp.getVariableNameDeclaration();
				Scope scope = fileVar.getScope();
				Map<VariableNameDeclaration, ArrayList<NameOccurrence>> varOccs = scope.getVariableDeclarations();
			    List<NameOccurrence> occs = varOccs.get(fileVar);
				for(NameOccurrence occ : occs) {
					tmpNode= occ.getLocation();
				//	VexNode vex=tmpNode.getFirstVexNode();
					ASTSelectionStatement stm1= (ASTSelectionStatement)tmpNode.getFirstParentOfType(ASTSelectionStatement.class);
					if(stm1!=null)
					{
						isChecked=true;
						break;
					}
				 }	
				if(!isChecked)
				addFSM(list,priExp,fsm);
			}
		}
		return list;
		
  }
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" The file stream " + node.getVariableNameDeclaration().getImage() + "in line " + node.getBeginLine() + "is unchecked for its validity.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("在第" + node.getBeginLine() + "行使用fopen函数打开文件 " + node.getVariableNameDeclaration().getImage() + "的操作未进行错误处理");
			}	
		
		list.add(fsminstance);
	}
}
