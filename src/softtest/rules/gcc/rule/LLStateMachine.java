package softtest.rules.gcc.rule;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.SimpleNode;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.interpro.c.InterContext;
import softtest.pretreatment.Pretreatment;

/**
 * @author Maojinyu
 * 建议一个过程或函数中的程序总行不超过200行
 * 建议一个文件中的程序总行不超过2000行
 * (版面书写类)
 */
public class LLStateMachine {	
	
	private static List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	//存储已经记录的文件节点（该文件中的程序总行不超过2000行）
	private static Set<ASTTranslationUnit> files = new HashSet<ASTTranslationUnit>();
	
	public static List<FSMMachineInstance> createLLMachines(SimpleNode node, FSMMachine fsm){
		
		//1. 针对过程或函数中的程序总行不超过200行
		String fileName = node.getFileName();
		int line = node.getEndLine() - node.getBeginLine();
		if(line > 200) {
			if(fileName==null || fileName.matches(InterContext.INCFILE_POSTFIX)) {//说明包含在编译库文件中
				return list;
			}
			FSMMachineInstance fsminstance = fsm.creatInstance();
			fsminstance.setRelatedASTNode(node);
			if(Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Proposed a method or function no more than 200 lines.");
			} else if(Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("建议一个文件中的过程或函数的总行不超过200行。\r\n在第"+node.getBeginFileLine()+"行的函数"+node.getImage()+"的总行数为" + line + "。");
			}	
			list.add(fsminstance);
		}
	
		//2. 针对文件中的程序总行不超过2000行		
		ASTTranslationUnit snode = (ASTTranslationUnit) node.getFirstParentOfType(ASTTranslationUnit.class);
		SimpleNode lastFunc = (SimpleNode) snode.jjtGetChild(snode.jjtGetNumChildren()-1);
		if(lastFunc.getEndLine() > 2000) {
			if(files.contains(snode)) {
				return list;
			} else {
				files.add(snode);
			}
			FSMMachineInstance fsminstance = fsm.creatInstance();
			if(Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
				fsminstance.setDesp("Proposed a file no more than 2000 lines.");
			} else if(Config.DTS_LANGUAGE == Config.LANG_CHINESE){
				fsminstance.setDesp("建议一个文件中的程序总行不超过2000行。\r\n该函数所在的文件 " + fileName + "总行数为" + lastFunc.getEndLine()+ "。");
			}	
			list.add(fsminstance);
		}	
		return list;
	}	
}
