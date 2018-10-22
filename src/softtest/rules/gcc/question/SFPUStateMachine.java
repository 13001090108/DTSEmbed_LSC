package softtest.rules.gcc.question;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTExternalDeclaration;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.SourceFileScope;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Pointer;

/** 
 * author yx
 * 模式：打印类型不匹配(Question:PRINT_FORMAT)
 */

public class SFPUStateMachine {
	
	enum Type {
		STRING, INTEGER, POINT, 
	}
	
	public static List<FSMMachineInstance> createSFPUStateMachines(SimpleNode node, FSMMachine fsm){
		
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();	
		List<SimpleNode> evaluationResults = new LinkedList<SimpleNode>();	
		
		String xpath = ".//PostfixExpression";

		evaluationResults = StateMachineUtils.getEvaluationResults(node, xpath);
		Iterator itr = evaluationResults.iterator();
		
		while(itr.hasNext()) {
			
			ASTPostfixExpression astpe = (ASTPostfixExpression)itr.next();
			
			int childNum = astpe.jjtGetNumChildren();
			
			if (childNum == 2) {
				ASTPrimaryExpression pre = (ASTPrimaryExpression)astpe.jjtGetChild(0);
				String preName = pre.getImage();
				
				ASTArgumentExpressionList astel = (ASTArgumentExpressionList)astpe.jjtGetChild(1);
				
				int childN = astel.jjtGetNumChildren();
				
				if ("sprintf".equals(preName) || "fprintf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					Type type1[];
					Type type2[];
					type1 = new Type[childN - 2];
					for (int i = 2; i < childN; ++i) {						
						ASTAssignmentExpression astaeChild = (ASTAssignmentExpression)astel.jjtGetChild(i);
						CType current = astaeChild.getType();
						String currentType = current.toString();
						
						if (currentType.contains("char")) 
							type1[i-2] = Type.STRING;						
						else if (currentType.contains("int") || currentType.contains("long") || currentType.contains("short"))
							type1[i-2] = Type.INTEGER;						
						else if (currentType.contains("double") || currentType.contains("float"))
							type1[i-2] = Type.POINT;
						else
							type1[i-2] = null;
					}
					
					type2 = getTypes(astaeName);
					
					boolean flag = true;
					
					flag = compare(type1, type2);

					if (!flag)
					    addFSM(list, astpe, fsm);
					
				} else if ("snprintf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					Type type1[];
					Type type2[];
					type1 = new Type[childN - 3];
					for (int i = 3; i < childN; ++i) {						
						ASTAssignmentExpression astaeChild = (ASTAssignmentExpression)astel.jjtGetChild(i);
						CType current = astaeChild.getType();
						String currentType = current.toString();
						
						if (currentType.contains("char")) 
							type1[i-2] = Type.STRING;						
						else if (currentType.contains("int") || currentType.contains("long") || currentType.contains("short"))
							type1[i-2] = Type.INTEGER;						
						else if (currentType.contains("double") || currentType.contains("float"))
							type1[i-2] = Type.POINT;
						else
							type1[i-2] = null;
					}
					
					type2 = getTypes(astaeName);
					
					boolean flag = true;
					
					flag = compare(type1, type2);

					if (!flag)
					    addFSM(list, astpe, fsm);
					
				} else if ("printf".equals(preName)) {

					ASTConstant astae = (ASTConstant)astel.getFirstChildOfType(ASTConstant.class);
					String astaeName = astae.getImage();
					
					Type type1[];
					Type type2[];
					type1 = new Type[childN - 1];
					for (int i = 1; i < childN; ++i) {						
						ASTAssignmentExpression astaeChild = (ASTAssignmentExpression)astel.jjtGetChild(i);
						CType current = astaeChild.getType();
						String currentType = current.toString();
						
						if (currentType.contains("char")) 
							type1[i-2] = Type.STRING;						
						else if (currentType.contains("int") || currentType.contains("long") || currentType.contains("short"))
							type1[i-2] = Type.INTEGER;						
						else if (currentType.contains("double") || currentType.contains("float"))
							type1[i-2] = Type.POINT;
						else
							type1[i-2] = null;
					}
					
					type2 = getTypes(astaeName);
					
					boolean flag = true;
					
					flag = compare(type1, type2);

					if (!flag)
					    addFSM(list, astpe, fsm);					
				}
			}
		}
		return list;
	}
	
	private static Type[] getTypes(String string) {
		
		String result[] = string.split("%");
		
		Type[] type2 = new Type[result.length-1];//第一个肯定是引号
		for (int i = 0; i < result.length; ++i) {
			
			char a[] = result[i].toCharArray();
			for (int j = 0; j < a.length; ++j) {
				if (a[j] == '"')
					continue;
				
				if (Character.isLetter(a[j])){	
					if ((a[j] == 'h') && (a[j+1] =='h')) {
						if (match1(a[j+2])) {
							type2[i-1] = Type.INTEGER;
							break;
						}
					} else if ((a[j] == 'l') && (a[j+1] == 'l')) {
						if (match1(a[j+2])) {
							type2[i-1] = Type.INTEGER;
							break;
						}else if (a[j+2] == 'c') {
							type2[i-1] = Type.STRING;	
							break;
						}
					} else if (a[j]=='h' || a[j]=='t' || a[j]=='z') {
						if (match1(a[j+1])) {
							type2[i-1] = Type.INTEGER;
							break;
						}		
					} else if (a[j]=='l') {
						if (match1(a[j+1])) {
							type2[i-1] = Type.INTEGER;
							break;
						} else if (a[j+2] == 'c') {
							type2[i-1] = Type.STRING;
							break;
						}						
					} else if (a[j] == 'L') {
						if (match2(a[j+1])) {
							type2[i-1] = Type.POINT;
							break;
						}						
					} else if (match1(a[j])) {
						type2[i-1] = Type.INTEGER;
						break;
					} else if (match2(a[j])) {
						type2[i-1] = Type.POINT;
						break;
					} else if (match3(a[j])) {
						type2[i-1] = Type.STRING;
						break;
					}
					break;
				}
			}			
		}		
		return type2;
	}
	
	private static boolean match1(char c) {
		
		if (c == 'u' || c == 'd' || c == 'x' || c == 'i' ||c =='X' || c =='o')
		    return true;
		
		return false;		
	}
	
	private static boolean match2(char c) {
		if (c == 'a' || c == 'A' || c == 'e' || c == 'E' ||c =='f' || c =='g' || c =='G')
		    return true;
		
		return false;	
	}
	
	private static boolean match3(char c) {
		if (c == 'c' || c == 'p' || c == 's')
			return true;
		
		return false;		
	}
	
	private static boolean compare(Type[] type1, Type[] type2) {
		
		for (int i = 0; i < type1.length; ++i) {
			if (type1[i] != type2[i]) {
				return false;
			}			
		}
		
		return true;
	}
	
	
	private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) {
		
		FSMMachineInstance fsminstance = fsm.creatInstance();
		fsminstance.setRelatedASTNode(node);
		
		if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp("Print type mismatch.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("打印类型不匹配。");
		}	
		list.add(fsminstance);
	}
}
