package softtest.rules.gcc.rule;

import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ArrayList;

import softtest.ast.c.*;
import softtest.config.c.Config;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.Type.*;
import softtest.symboltable.c.*;

/** 
 * @author LiuChang
 * 结构体变量初始化的类型不一致
 * InconsistentInitialTypeOfStruct
 */

public class IITSStateMachine {

	public static List<FSMMachineInstance> createIITSStateMachines(SimpleNode node, FSMMachine fsm){
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
	    List<SimpleNode> evaluationResults = null;
	    List<SimpleNode> defineResults = null;
	    List<SimpleNode> typeResults = null;
		String xPath = ".//Declaration/InitDeclaratorList/InitDeclarator[./Initializer]//Declarator/DirectDeclarator";
		String path = ".//Declaration/DeclarationSpecifiers/TypeSpecifier/StructOrUnionSpecifier[./StructDeclarationList]";
		String ath = ".//Declaration[./InitDeclaratorList]/DeclarationSpecifiers//TypeSpecifier/StructOrUnionSpecifier";
		evaluationResults = StateMachineUtils.getEvaluationResults(node, xPath);
		defineResults = StateMachineUtils.getEvaluationResults(node, path);
		typeResults = StateMachineUtils.getEvaluationResults(node, ath);
		Iterator itr = evaluationResults.iterator();
        Iterator itr1 = typeResults.iterator();
		while(itr.hasNext()&&itr1.hasNext()){
			ASTStructOrUnionSpecifier id3 = (ASTStructOrUnionSpecifier)itr1.next();
			CType type = id3.getType();
			ASTDirectDeclarator qualifiedId = (ASTDirectDeclarator)itr.next();

			if(type == null)
				continue;
			if(type instanceof CType_Struct);{
	        SimpleNode definitionNode = findStructDefinitionNode(type,defineResults);
			if(definitionNode == null)
				continue;
			SimpleNode spcecifier = (SimpleNode)definitionNode.getFirstChildOfType(ASTStructDeclarationList.class);
												
			SimpleNode snode = (SimpleNode)qualifiedId.getFirstParentOfType(ASTInitDeclarator.class);
			if(snode == null)
				continue;
			if(snode.jjtGetNumChildren() != 2 || !(snode.jjtGetChild(1) instanceof ASTInitializer) )
				continue;
			snode = (SimpleNode)snode.getFirstChildOfType(ASTInitializerList.class);
				
			findInconsitancy(list,snode,spcecifier,fsm);
			}}
		
		return list;
	
  }
	
	/**
	 * 找到对应struct结构体定义节点，无则返回null*/	
	public static SimpleNode findStructDefinitionNode(CType init,List<SimpleNode> list){
		if(list == null)
			return null;

		Iterator itr = list.iterator();
		while(itr.hasNext())
		{
			ASTStructOrUnionSpecifier id = (ASTStructOrUnionSpecifier)itr.next();
			CType type=id.getType();
			
			if(type == null)
				continue;
			if(init.equals(type)){
				return id;
			}
		}
			return null;
	}

	
	public static List<SimpleNode> findMemberList(List<SimpleNode> list){
		List<SimpleNode> memberList = new ArrayList<SimpleNode>();
		for(SimpleNode member : list){
			if(member.jjtGetNumChildren() == 1 && member.jjtGetChild(0) instanceof ASTDeclaration)
				memberList.add((SimpleNode)member.jjtGetChild(0));
			else if(member.jjtGetNumChildren() == 0)
				continue;
			else if(member.jjtGetChild(0) instanceof ASTSpecifierQualifierList)
				memberList.addAll((Collection<? extends SimpleNode>) member.findChildrenOfType(ASTStructDeclarator.class));
		}
		return memberList;
	}
	
	/**
	 * 判断非结构变量初始化的类型是否一致，对应IITS
	 * */
	public static boolean different(SimpleNode member,SimpleNode init){
		SimpleNode id =(SimpleNode)member.getFirstParentOfType(ASTStructDeclaratorList.class);

		if(id == null)
			return false;
		id = (SimpleNode)id.getFirstChildOfType(ASTDirectDeclarator.class);
		if(id == null)
			return false;
		ASTDirectDeclarator qualifiedId = (ASTDirectDeclarator)id;
		CType memberType = qualifiedId.getType();
		SimpleNode check = (SimpleNode)id.getFirstParentOfType(ASTStructDeclaration.class);
		SimpleNode typ = (SimpleNode)check.getFirstChildOfType(ASTStructOrUnionSpecifier.class);
		ASTStructOrUnionSpecifier type = (ASTStructOrUnionSpecifier)typ;
		if(type != null)
			return false;
		if(init.jjtGetNumChildren() != 1)
			return true;
		ASTAssignmentExpression ass =(ASTAssignmentExpression)init.jjtGetChild(0);
		CType initType = ass.getType();
		if(initType.equals(memberType))
			return false;
		else return true;
		
	}
	

	
	
	public static void findInconsitancy(List<FSMMachineInstance> list, SimpleNode snode,  SimpleNode spcecifier, FSMMachine fsm){
		
		List<SimpleNode> memList = new ArrayList<SimpleNode>();
		memList = spcecifier.findDirectChildOfType(ASTStructDeclaration.class);
		List<SimpleNode> memberList = new ArrayList<SimpleNode>();
		memberList = findMemberList(memList);
		
		List<SimpleNode> initList = new ArrayList<SimpleNode>();
		if(snode == null)
			return;
		initList = snode.findDirectChildOfType(ASTInitializer.class);
		//允许部分初始化。即初始化的元素个数可以小于等于struct定义时的声明
		if(initList.size() > memberList.size())
			return;
	
		Iterator initItr = initList.iterator();
		Iterator memberItr = memberList.iterator();

		while(initItr.hasNext() && memberItr.hasNext()){
			SimpleNode member = (SimpleNode)memberItr.next();
			SimpleNode init = (SimpleNode)initItr.next();
			if(member instanceof ASTStructDeclarator){
				if(different(member,init))
					addFSM(list,init,fsm);
			}	

			}	
		}
	




private static void addFSM(List<FSMMachineInstance> list, SimpleNode node, FSMMachine fsm) 

{
	FSMMachineInstance fsminstance = fsm.creatInstance();
	fsminstance.setRelatedASTNode(node);
	if (Config.DTS_LANGUAGE == Config.LANG_ENGLISH) {
			fsminstance.setDesp(" IITS： The initial type of struct must be the same with definition.");
		} else if (Config.DTS_LANGUAGE == Config.LANG_CHINESE){
			fsminstance.setDesp("结构体变量初始化的类型不一致: 结构体变量的初值类型必须与结构体变量的定义类型一致。");
		}	
	
	list.add(fsminstance);
}


}