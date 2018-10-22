package softtest.rules.gcc.rule;

import java.util.LinkedList;
import java.util.List;


import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;


/** 
 * @author LiuChang
 * Signed Bit Field Exceed Two
 * 有符号类型的位长度必须大于等于两位(char类型暂当有符号数，书上说根据编译器而定)
 * (运算处理类)
 */
public class SBFETStateMachine {
	
	//找到所有的结构声明
	private static String xpath = ".//DeclarationSpecifiers/TypeSpecifier/StructOrUnionSpecifier[./StructOrUnion[@Image='struct']]";
	//找到结构中的形如'a:1','a:0'的成员变量（避免空占位，如 int :2形式）
	private static String xpath1 = ".//StructDeclaration[./StructDeclaratorList/StructDeclarator/ConstantExpression/UnaryExpression/PostfixExpression/PrimaryExpression/Constant[@Image='0' or @Image='1']]/SpecifierQualifierList";
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	private static List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();
	
	public static List<FSMMachineInstance> createSBFETMachines(SimpleNode node, FSMMachine fsm){
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		List<SimpleNode> members = new LinkedList<SimpleNode>();
		
		for (SimpleNode snode : evaluationResults) {
			members = StateMachineUtils.getEvaluationResults(snode, xpath1);//找到结构中的形如'a:1','a:0'的成员变量
		
			for(SimpleNode member : members) {
				//如果是short a:1 或 int a:0 类型
				if(member.jjtGetNumChildren() == 1) {
					SimpleNode memberType = (SimpleNode) member.jjtGetChild(0);
					if(isSigned(memberType.getImage())) //如果a是有符号数,即a的位长度是1或0
						addFSMDescription(member, fsm);
				}
				//如果是unsigned short a:1 或 signed int a:1 类型
				else if(member.jjtGetNumChildren() > 1) {
					SimpleNode first = (SimpleNode) member.jjtGetChild(0);
					if(first.getImage()!=null  && first.getImage().equalsIgnoreCase("signed"))
							addFSMDescription(member, fsm);
				}	
			}
		}
	    return list;
	}	
	
	/*
	 * 因为还有个规则为位的定义必须是有符号整数或无符号整数，
	 * 暂考虑long,longLong类型（下个规则模式会将其报出）
	 */
	private static boolean isSigned(String str) {
		if("int".equalsIgnoreCase(str) || "short".equalsIgnoreCase(str)  || "long".equalsIgnoreCase(str) || "longLong".equalsIgnoreCase(str) || "char".equalsIgnoreCase(str)) 
			return true;
		else 
			return false;
	}

	private static void addFSMDescription( SimpleNode node, FSMMachine fsm) {
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Bit Filed of Signed Number should exceed or equal to Two");
			} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("有符号数的位长度应该大于等于2。\r\n有符号类型只给一位的长度是没有意义的。");
			}	
		
		list.add(fsminstance);
	}
}
