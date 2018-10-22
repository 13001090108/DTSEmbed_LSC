package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.fsm.c.FSMRelatedCalculation;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.VariableNameDeclaration;


/**
 * @author 
 * @DD means Declaration and Definition
 * @1st:没有边界限定的数组定义.
 */
public class DDStateMachine {
	
	public static List<FSMMachineInstance> createDDStateMachines(
			SimpleNode node, FSMMachine fsm) {
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		String xPath = ".//Declaration/InitDeclaratorList/InitDeclarator/Declarator/DirectDeclarator[@Operators='[']";
		List<SimpleNode> evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		for (SimpleNode snode : evaluationResults){
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(snode);
			fsminstance.setRelatedObject(new FSMRelatedCalculation(snode));
			list.add(fsminstance);
		}
		return list;
	}
	public static boolean checkArrayDecIsNull(List<SimpleNode> nodes, FSMMachineInstance fsmin){
		boolean result=false;
		SimpleNode simnode=fsmin.getRelatedASTNode();
		for(SimpleNode node:nodes){
			if(simnode!=node)
				continue;
			ASTDirectDeclarator decnode=(ASTDirectDeclarator)simnode;
			VariableNameDeclaration varname=(VariableNameDeclaration)decnode.getDecl();
			
			fsmin.setRelatedVariable(varname);
			if(decnode.jjtGetNumChildren()==0){
				result=true;
				addFSMDescription(varname,fsmin);
			}
		}
		return result;
	}
	private static void addFSMDescription(VariableNameDeclaration variable, FSMMachineInstance fsminstance) {
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" This Array Should Init With Num " + variable.getFileName());
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("对数组" + variable.getFileName() + "进行声明时没有声明边界");
			}	
	}
}
