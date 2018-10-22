package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.pretreatment.Pretreatment;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;

/** 
 * @author LiuChang
 * Bit Define Be Int(unsigned or signed)
 * 位的定义必须是有符号整数或无符号整数
 */
public class BDBIStateMachine {
	
	public static List<FSMMachineInstance> createBDBIMachines(SimpleNode node, FSMMachine fsm){
		//找到所有的结构申明
		String xpath = ".//DeclarationSpecifiers/TypeSpecifier/StructOrUnionSpecifier[./StructOrUnion[@Image='struct']]";
		//找到结构中的位域的成员变量，避免空占位如 int :2形式
		String xpath1 = ".//StructDeclaration[./StructDeclaratorList/StructDeclarator/ConstantExpression/UnaryExpression/PostfixExpression/PrimaryExpression/Constant]/SpecifierQualifierList";
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
		
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		List<SimpleNode> members = new LinkedList<SimpleNode>();
		
		for (SimpleNode snode : evaluationResults) {
			members = StateMachineUtils.getEvaluationResults(snode, xpath1);//找到结构中的形如'a:3'的成员变量
		
			for(SimpleNode member : members) {
				//如果是库的头文件，忽略之
				String fileName = member.getFileName();
				if(fileName == null || isSysInc(fileName))//说明包含在编译库文件中
					continue;	
				
				//如果是int a:3 类型
				if(member.jjtGetNumChildren() == 1) {
					SimpleNode memberType = (SimpleNode) member.jjtGetChild(0);
					if(!(memberType.getImage().equalsIgnoreCase("int")))//如果member不是int类型
						addFSMDescription(member, fsm, list);
				}
				//如果是unsigned int a:4 类型
				else if(member.jjtGetNumChildren() == 2) {
					SimpleNode first = (SimpleNode) member.jjtGetChild(0);
					SimpleNode second = (SimpleNode) member.jjtGetChild(1);
					//如果member不是unsigned int
					if(!(first.getImage().equalsIgnoreCase("unsigned") && second.getImage().equalsIgnoreCase("int"))) { 
							addFSMDescription(member, fsm, list);
					}
				}	
			}
		}
	    return list;
	}	
	static String systemInc[] = new String[0];
	static boolean isSysInc(String fileName) {
		for (int i = 0; i < systemInc.length; i++) {
			if (fileName.startsWith(systemInc[i])) {
				return true;
			}
		}
		return false;
	}
	
	private static void addFSMDescription( SimpleNode node, FSMMachine fsm, List<FSMMachineInstance> list) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp(" The Define of Bit filed should be int or unsigned int.");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("位的定义必须是有符号整数或无符号整数。\r\n位不能定义为有符号或无符号整数之外的其它类型。");
			}	
		
		list.add(fsminstance);
	}
}
