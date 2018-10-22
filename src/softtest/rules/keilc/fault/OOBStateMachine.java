package softtest.rules.keilc.fault;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import softtest.ast.c.*;
import softtest.rules.c.BasicStateMachine;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;
import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.interval.*;
import softtest.domain.c.symbolic.Expression;
import softtest.fsm.c.*;
/**
 * 
 *   modified by chh
 *
 */
public class OOBStateMachine extends BasicStateMachine{
	private static int OOBNO = 0;
	// 每个数组产生一个状态机
	public static List<FSMMachineInstance> createOOBStateMachines(SimpleNode node, FSMMachine fsm) {
	
		List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
		// 仅在数组使用的时候创建状态机 a[1] = 1;
		String xpath = ".//UnaryExpression/PostfixExpression[contains(@Operators,'[')]" ;
			
		List evaluationResults = node.findXpath(xpath);
		
		Set<VariableNameDeclaration> varset = new HashSet<VariableNameDeclaration>();
		
out:	for (Object snode : evaluationResults) {
			ASTPostfixExpression post = (ASTPostfixExpression) snode;
			ASTPrimaryExpression primary=(ASTPrimaryExpression)post.jjtGetChild(0);
			VariableNameDeclaration curvar;
			if(primary.getFirstParentOfType(ASTLogicalANDExpression.class)!=null)
				continue;
			//chh  指针引用方式和数组引用方式分别处理   例如：((char *)buf)[2]=3;
			if(primary.getVariableDecl()!=null){
				curvar=primary.getVariableDecl();
			}else {
				primary=(ASTPrimaryExpression)primary.getFirstChildOfType(ASTPrimaryExpression.class);
				if(primary==null)//typedef char cc;i=sizeof(cc[5]);
					continue;
				curvar=primary.getVariableDecl();
			}
			//end
			ArrayList<Boolean> flags=post.getFlags();
			ArrayList<String> operators=post.getOperatorType();
			int j=1;
			for(int i=0;i<flags.size();i++){
				boolean flag=flags.get(i);
				String operator=operators.get(i);
				if(operator.equals("[")){
					if(flag){
						j++;
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					if(curvar!=null&&!varset.contains(curvar)&&!curvar.isParam()){
						FSMMachineInstance fsminstance = fsm.creatInstance();
						fsminstance.setRelatedVariable(curvar);
						fsminstance.setRelatedASTNode((SimpleNode)snode);
						varset.add(curvar);
						list.add(fsminstance);
						OOBNO++;
					}
				}else if(operator.equals("(")){
					continue out;
				}else if(operator.equals(".")){
					ASTFieldId field=null;
					if(flag){
						field=(ASTFieldId)post.jjtGetChild(j++);
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					curvar=field.getVariableNameDeclaration();
				}else if(operator.equals("->")){
					ASTFieldId field=null;
					if(flag){
						field=(ASTFieldId)post.jjtGetChild(j++);
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					curvar=field.getVariableNameDeclaration();
				}else{
					//do nothing
				}
			}
		}
		//chh  char c = *(buf+4);为了检测此类故障，对声明的数组创建自动机
		xpath=".//AssignmentExpression/UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression/PrimaryExpression/Expression/AssignmentExpression/AdditiveExpression";
		evaluationResults = node.findXpath(xpath);
		for (Object snode : evaluationResults) {
			ASTPrimaryExpression primary=(ASTPrimaryExpression) ((ASTAdditiveExpression) snode).getFirstChildInstanceofType(ASTPrimaryExpression.class);
			VariableNameDeclaration curvar = primary.getVariableNameDeclaration();
			if(primary.getFirstParentOfType(ASTLogicalANDExpression.class)!=null)
				continue;
			if(curvar!=null&&curvar.getType()!=null&&(curvar.getType() instanceof CType_Array||curvar.getType().isPointType())
					&&!curvar.isParam()) 
			{
					FSMMachineInstance fsminstance = fsm.creatInstance();
					fsminstance.setRelatedVariable(curvar);
					fsminstance.setRelatedASTNode((SimpleNode)snode);
					list.add(fsminstance);
					OOBNO++;
				
			}
			else continue;
		}//end
		xpath=".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression[contains(@Operators,'++')]/UnaryExpression/PostfixExpression/PrimaryExpression|" +
				".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression[contains(@Operators,'++')]/PrimaryExpression|" +
				".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression[contains(@Operators,'--')]/UnaryExpression/PostfixExpression/PrimaryExpression|" +
				".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression[contains(@Operators,'--')]/PrimaryExpression";
		evaluationResults = node.findXpath(xpath);
		for (Object snode : evaluationResults) {
			ASTPrimaryExpression primary=(ASTPrimaryExpression) snode;
			if(primary.getFirstParentOfType(ASTLogicalANDExpression.class)!=null)
				continue;
			VariableNameDeclaration curvar = primary.getVariableNameDeclaration();
			if(curvar!=null&&curvar.getType()!=null&&curvar.getType().isPointType()&&!curvar.isParam()) 
			{
					FSMMachineInstance fsminstance = fsm.creatInstance();
					fsminstance.setRelatedVariable(curvar);
					fsminstance.setRelatedASTNode((SimpleNode)snode);
					list.add(fsminstance);
					OOBNO++;
				
			}
			else continue;
		}
		return list;
	}
	/*
	 * // chh   “char c = *(buf+4)，buf为4个元素的数组”此类故障单独检测
	 **/
	public static boolean checkSameVariableAndOOB0(VariableNameDeclaration variable,FSMMachineInstance fsmin){
		
		ASTAdditiveExpression addexp=(ASTAdditiveExpression)fsmin.getRelatedASTNode();
		VariableNameDeclaration curvar=variable;
		IntegerInterval size=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
		IntegerInterval usesize=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
		if(curvar.getType().isArrayType())	{	
			CType curtype=curvar.getType();
			CType type=curtype.getSimpleType();
			CType_Array atype=(CType_Array)type;
			size=new IntegerInterval(0,atype.getDimSize()-1);
			if(size.getMax()==0) return false;
		}
		else if(!curvar.getType().isArrayType()&&curvar.getType().isPointType()){
			ASTPrimaryExpression primary=(ASTPrimaryExpression) ((ASTAdditiveExpression) addexp).getFirstChildInstanceofType(ASTPrimaryExpression.class);
			size=OOBStateMachine.getrange(primary, curvar);
			if(size.getMax()==Long.MIN_VALUE&&size.getMin()==Long.MIN_VALUE) return false;
		}
		for(int k=1;k<addexp.jjtGetNumChildren();k++)
		{
			if(addexp.jjtGetChild(k) instanceof ASTUnaryExpression)
			{
				ASTPrimaryExpression child=(ASTPrimaryExpression) ((SimpleNode) addexp.jjtGetChild(k)).getFirstChildOfType(ASTPrimaryExpression.class);
				ExpressionValueVisitor expvst = new ExpressionValueVisitor();
				ExpressionVistorData visitdata = new ExpressionVistorData();
				visitdata.currentvex = child.getCurrentVexNode();
				visitdata.currentvex.setfsmCompute(true);
				expvst.visit(child, visitdata);
				visitdata.currentvex.setfsmCompute(false);
				Expression value1 = visitdata.value;
				Domain mydomain=null;
				if(value1!=null)
				mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
				if((mydomain instanceof IntegerDomain)&&((IntegerDomain)mydomain).getMin()==((IntegerDomain)mydomain).getMax()){
					usesize.setMin(usesize.getMin()+((IntegerDomain)mydomain).getMin());
					usesize.setMax(usesize.getMax()+((IntegerDomain)mydomain).getMax());
				}
				else {
					return false;
				}	
			}
			else{ 
				return false;
			}
		}
		if(!(size.getMax()==Long.MAX_VALUE&&size.getMin()==Long.MIN_VALUE)&&
				(usesize.getMax()>size.getMax()||usesize.getMin()<size.getMin())
				&&!curvar.isParam()){
			fsmin.setDesp("在第 " + curvar.getNode().getBeginLine() + " 行定义的大小为 " + (size.getMax()-size.getMin()+1) + " 的指针或数组\""+curvar.getImage()+"\"可能在第"+addexp.getBeginLine()+"行越界 ");
			fsmin.setNodeUseToFindPosition(addexp);
			return true;
		}
		else return false;
	
	}
	public static boolean checkSameVariableAndOOB(List nodes, FSMMachineInstance fsmin) {
		
		Iterator itor = nodes.iterator();
out:	while (itor.hasNext()) {
		SimpleNode snode=(SimpleNode)itor.next();
			//chh   检测.//AssignmentExpression/UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression/PrimaryExpression/Expression/AssignmentExpression/AdditiveExpression”
			if(snode instanceof ASTAdditiveExpression && fsmin.getRelatedASTNode() instanceof ASTAdditiveExpression
					&&snode==fsmin.getRelatedASTNode()){
				if(checkSameVariableAndOOB0(fsmin.getRelatedVariable(),fsmin)&&!fsmin.getRelatedVariable().isParam())
					return true;
			}
			/*chh 检测".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression[contains(@Operators,'++')]/UnaryExpression/PostfixExpression/PrimaryExpression|" +
			".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression[contains(@Operators,'++')]/PrimaryExpression|" +
			".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression[contains(@Operators,'--')]/UnaryExpression/PostfixExpression/PrimaryExpression|" +
			".//UnaryExpression[/UnaryOperator[1][contains(@Operators,'*')]]/UnaryExpression/PostfixExpression[contains(@Operators,'--')]/PrimaryExpression";*/
			else if(snode instanceof ASTPrimaryExpression&&!fsmin.getRelatedVariable().isParam()
					&&snode==fsmin.getRelatedASTNode()){
				IntegerInterval range=getrange((ASTPrimaryExpression) snode,fsmin.getRelatedVariable());
				if(range.getMax()<0&&!(range.getMax()==Long.MAX_VALUE && range.getMin()==Long.MIN_VALUE)) {
					fsmin.setDesp("在第 " + fsmin.getRelatedVariable().getNode().getBeginLine() + " 行定义的指针\""+fsmin.getRelatedVariable().getImage()+"\"可能在第"+snode.getBeginLine()+"行越界，目前偏移区间： "+range);
					fsmin.setNodeUseToFindPosition(snode);
					return true;
				}
			}
			//chh   检测.//UnaryExpression/PostfixExpression[contains(@Operators,'[')]找到的节点，针对  “带‘[’的数组使用出现”
			else if(snode instanceof ASTPostfixExpression&&(fsmin.getRelatedASTNode()) instanceof ASTPostfixExpression
					)
			{
			
			ASTPostfixExpression post = (ASTPostfixExpression) snode;
			ASTPrimaryExpression primary=(ASTPrimaryExpression)post.jjtGetChild(0);
			VariableNameDeclaration curvar;
			//chh  指针引用方式((char *)array)[]/(pointer+?)[]和数组引用方式array[]分别处理
			if(primary.getVariableDecl()!=null)
				curvar=primary.getVariableDecl();
			else{
				primary=(ASTPrimaryExpression)primary.getFirstChildOfType(ASTPrimaryExpression.class);
				if(primary==null)
					continue;
				curvar=primary.getVariableDecl();
			}
			//end
			if(curvar==null||curvar.getType()==null){
				continue;
			}
			CType curtype=curvar.getType();
			
			ArrayList<Boolean> flags=post.getFlags();
			ArrayList<String> operators=post.getOperatorType();
			int j=1;
			for(int i=0;i<flags.size();i++){
				boolean flag=flags.get(i);
				String operator=operators.get(i);
				if(operator.equals("[")){
					ASTExpression expression =null;
					CType type=curtype.getSimpleType();
					if(flag){
						expression=(ASTExpression)post.jjtGetChild(j++);
						if(curvar==fsmin.getRelatedVariable()){
							//检查越界
							VexNode vex=post.getCurrentVexNode();

							if(curtype!=null&&(curtype instanceof CType_Array||curtype.isPointType())){
								CType_Array atype=null;
								IntegerInterval size=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
								// 指针引用方式pointer[]和数组引用方式array[]分别处理
								if(curtype instanceof CType_Array)
								{
									atype=(CType_Array)type;
									if(atype.getDimSize()!=-1&&atype.getDimSize()!=0)
										size=new IntegerInterval(0,atype.getDimSize()-1);
									else 
										size=new IntegerInterval(0,0);
									if(size.getMax()==0)
										return false;
								}
								else if(!(curtype instanceof CType_Array)&&curtype.isPointType())
								{
									size=OOBStateMachine.getrange(primary, curvar);
									if(size.getMin()==Long.MIN_VALUE&&size.getMax()==Long.MAX_VALUE||
											(size.getMax()==0&&size.getMin()==0))
										return false;
								}
								// (buf+i-j)[3]='c';//暂不考虑其中i，j为参数和全局变量的情况
								if(primary.getFirstParentOfType(ASTAdditiveExpression.class)!=null
										&&primary.getFirstParentOfType(ASTPrimaryExpression.class)!=null
										&&((SimpleNode)((ASTPrimaryExpression)primary.getFirstParentOfType(ASTPrimaryExpression.class)).jjtGetParent()).getOperators().equals("["))
								{
									SimpleNode parent=(SimpleNode) primary.getFirstParentOfType(ASTAdditiveExpression.class);
									for(int k=1;k<parent.jjtGetNumChildren();k++)
									{
										if(parent.jjtGetChild(k) instanceof ASTUnaryExpression)
										{
											ASTPrimaryExpression child=(ASTPrimaryExpression) ((SimpleNode) parent.jjtGetChild(k)).getFirstChildOfType(ASTPrimaryExpression.class);
											ExpressionValueVisitor expvst = new ExpressionValueVisitor();
											ExpressionVistorData visitdata = new ExpressionVistorData();
											visitdata.currentvex = child.getCurrentVexNode();
											visitdata.currentvex.setfsmCompute(true);
											expvst.visit(child, visitdata);
											visitdata.currentvex.setfsmCompute(false);
											Expression value1 = visitdata.value;
											Domain mydomain=null;
											if(value1!=null)
											mydomain = value1.getDomain(visitdata.currentvex.getLastsymboldomainset());
											if((mydomain instanceof IntegerDomain)&&((IntegerDomain)mydomain).getMin()==((IntegerDomain)mydomain).getMax()){
												size.setMax(size.getMax()-((IntegerDomain)mydomain).getMax());
												size.setMin(size.getMin()-((IntegerDomain)mydomain).getMin());
											}
											else{ 
												size=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
												break;
											}
										}
										else{ 
											size=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
											break;
										}
									}
								
								}
								//end
								if(vex!=null && expression.getDomain(vex) != null){
									IntegerDomain idomain=Domain.castToIntegerDomain(expression.getDomain(vex));
									if(!(size.getMax()==Long.MAX_VALUE&&size.getMin()==Long.MIN_VALUE)
											&&idomain!=null&&(size.getMax()<idomain.getMax()||size.getMin()>idomain.getMin())
											&&!curvar.isParam()&&idomain.getMax()!=Long.MAX_VALUE&&idomain.getMin()!=Long.MIN_VALUE){//&&idomain.getMax()!=Long.MAX_VALUE
										fsmin.setDesp("在第 " + curvar.getNode().getBeginLine() + " 行定义的大小为 " +size+ " 的数组或指针\""+curvar.getImage()+"\"可能在第"+snode.getBeginLine()+"行越界 ，index："+idomain);
										fsmin.setNodeUseToFindPosition(snode);
										return true;
									}	
								}
							}
						}
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					
					if(type instanceof CType_AbstPointer){
						CType_AbstPointer ptype=(CType_AbstPointer) type;
						curtype=ptype.getOriginaltype();
					}
				}else if(operator.equals("(")){
					continue out;
				}else if(operator.equals(".")){
					ASTFieldId field=null;
					if(flag){
						field=(ASTFieldId)post.jjtGetChild(j++);
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					curvar=field.getVariableNameDeclaration();
					if(curvar==null)
						continue out;
					else
						curtype=curvar.getType();
				}else if(operator.equals("->")){
					ASTFieldId field=null;
					if(flag){
						field=(ASTFieldId)post.jjtGetChild(j++);
					}else{
						throw new RuntimeException("ASTPostfixExpression error!");
					}
					curvar=field.getVariableNameDeclaration();
					if(curvar==null)
						continue out;
					else
						curtype=curvar.getType();
				}else{
					//do nothing
				}
			}
		  }
		
		}
		return false;
	}
	public static IntegerInterval getrange(ASTPrimaryExpression snode,VariableNameDeclaration var){
		IntegerInterval size= new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
		ExpressionValueVisitor expvst = new ExpressionValueVisitor();
		ExpressionVistorData visitdata = new ExpressionVistorData();
		visitdata.currentvex = snode.getCurrentVexNode();
		visitdata.currentvex.setfsmCompute(true);
		expvst.visit(snode, visitdata);
		visitdata.currentvex.setfsmCompute(false);
		Expression value1 = visitdata.currentvex.getValue(var);
		PointerDomain mydomain=null;
		
			try
			{
				if(value1!=null && value1.getDomain(visitdata.currentvex.getSymDomainset())!=null&&value1.getDomain(visitdata.currentvex.getSymDomainset()).getDomaintype()== DomainType.POINTER)
				mydomain = (PointerDomain) value1.getDomain(visitdata.currentvex.getSymDomainset()).clone();
			} catch (CloneNotSupportedException e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		
		if(mydomain!=null&&mydomain.offsetRange!=null){
			IntegerInterval Len=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);
			//temp用于存放每个空间的长度
			for (IntegerInterval range : mydomain.offsetRange.intervals) {
				if(range.getMax()==Long.MAX_VALUE||range.getMin()==Long.MIN_VALUE
						||(range.getMax()==range.getMin()))
					//防止  char *p=计算不出的表达式，*q=p+1；此时q的offsetRange为{-1，-1}
					{
					Len=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE);	
					break;
					}
				if(range.getMax()<Len.getMax())
					Len.setMax(range.getMax());
				if(range.getMin()>Len.getMin())
					Len.setMin(range.getMin());
			}
			if(Len.getMax()!=Long.MAX_VALUE&&Len.getMin()!=Long.MIN_VALUE)
				size=Len;
		}
		return size;
	}
	//判断字符串是否含有非数字字符
	public static boolean isNum(String str){ 
		if(str==null||str.isEmpty()){
			return false;
		}
        String   patternStr= "\\d\\.?\\d*";    
        Pattern   p=Pattern.compile(patternStr);     
        Matcher   m=p.matcher(str); 
        boolean   b=m.matches();
		return b;
	}
	public static int getOOBNO(){
		return OOBNO;
	}
}
