package softtest.domain.c.analysis;

import java.util.*;

import softtest.ast.c.*;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DomainType;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.NumberFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.interpro.c.Method;
import softtest.interpro.c.InterContext;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AbstPointer;
import softtest.symboltable.c.Type.CType_AllocType;
import softtest.symboltable.c.Type.CType_Enum;
import softtest.symboltable.c.Type.CType_Pointer;
import softtest.symboltable.c.Type.CType_Struct;
import softtest.symboltable.c.Type.CType_Union;

/** 用于区间运算的控制流图访问者 */
public class DomainVexVisitor implements GraphVisitor {
	
	//上一个处理的节点的编号
	int lastVexNodeNumber=0;
	
	static int looplayer = 0;
		
	List<String> loopNodeNames = null;
	List<String> loopOutNodeNames = null;
	
	private void calculateIN(VexNode n, Object data) {

		if(n.getName().startsWith("func_head"))
		{			
			looplayer = 0;
			
			loopNodeNames = new ArrayList<String>();
			loopOutNodeNames = new ArrayList<String>();
			
			return;
		}
		if (n.getValueSet() != null) {
			n.getValueSet().clearValueSet();
		}
		
		if (n.getName().startsWith("while_head") || n.getName().startsWith("for_head") || n.getName().startsWith("do_while_out1")) {
			n.setLoopHead(true);
			if(!loopNodeNames.contains(n.getName()))
			{
				looplayer ++;
				loopNodeNames.add(n.getName());
			}
		}else
		{
			n.setLoopHead(false);
		}
		
		if (n.getName().startsWith("while_out") || n.getName().startsWith("for_out") || n.getName().startsWith("do_while_out2")) 
		{
			if(!loopOutNodeNames.contains(n.getName()))
			{
				looplayer --;
				loopOutNodeNames.add(n.getName());
			}
		}

		List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = n.getInedges().elements(); e.hasMoreElements();) {
			Edge edge=e.nextElement();
			list.add(edge);
		}
		
		Collections.sort(list);
		
		/**dongyk 20120306 统计for循环执行的次数 */
		int forExecuteTimes=0;
		
		for (Edge edge : list) {
			forExecuteTimes++;
			VexNode pre = edge.getTailNode();
			ValueSet valueset=pre.getValueSet();
			SymbolDomainSet domainset=pre.getSymDomainset();
			
			//董玉坤 20120829 如果前驱是程序终止节点，则不处理
			if(pre.getName().startsWith("exit")||pre.getName().startsWith("abort"))
			{
				edge.setContradict(true);
				continue;
			}
						
			// 判断分支是否矛盾
			if (edge.getContradict()) {
				continue;
			}

			// 如果前驱节没有访问过则跳过
			if (!pre.getVisited()) {
				continue;
			}
			
			/**dongyk 20120306 n是循环头节点，并且循环至少执行了一次，则舍弃第一个前驱节点 */
			if(n.isLoopHead()&&n.getLoopExecuteAtleastOnce()&&forExecuteTimes==1&&lastVexNodeNumber>getNodeNum(n)){
				continue;
			}
			/**dongyk 20120306 n是循环头节点，并且循环至少执行了一次，重新设置n中的区间值 */
			
			if(n.isLoopHead()&&n.getLoopExecuteAtleastOnce()&&forExecuteTimes==2&&lastVexNodeNumber>getNodeNum(n)){
				n.setLastsymboldomainset(domainset);
				n.setLastvalueset(valueset);
				n.setSymDomainset(domainset);				
				n.setVarDomainSet(pre.getVarDomainSet());			
			}

			if (edge.getName().startsWith("T")) {
				//zys:如果是循环之后的真分支
				if (pre.getName().startsWith("while_head") || pre.getName().startsWith("for_head") || pre.getName().startsWith("do_while_out1")) {
					ConditionData condata = pre.getCondata();
						//for(; ;) while(i<1);
						if(condata!=null){
							SymbolDomainSet ds = condata.getTrueMayDomainSet();
							SymbolDomainSet dsTrue=condata.getTrueMustDomainSet();
							
							if(dsTrue.contains(domainset))
							{
								pre.setLoopExecuteAtleastOnce(true);
							}
							
							domainset=SymbolDomainSet.intersect(domainset, ds);							
							if(!domainset.isContradict()){
								domainset=SymbolDomainSet.union(domainset, ds);
							} 
							n.mergeValueSet(valueset,domainset);
						}
				}else{
					ConditionData condata = pre.getCondata();
					if (condata != null) {
						SymbolDomainSet ds = condata.getTrueMayDomainSet();
						domainset=SymbolDomainSet.intersect(domainset, ds);
						if(domainset.isContradict()){
							edge.setContradict(true);
							//zys:2010.4.23
							continue;
						}else{
							n.mergeValueSet(valueset,domainset);
						}
					}else{				
						n.mergeValueSet(valueset,domainset);
					}
				}
			} else if (edge.getName().startsWith("F")) {
				// 处理一次循环
				if (n.getName().startsWith("while_out") || n.getName().startsWith("for_out") || n.getName().startsWith("do_while_out2")) {
					
					if(!Config.LOOPCAL||looplayer > Config.LOOPLAYER)
					{
						visit(pre, data);
						domainset = pre.getSymDomainset();
						valueset=pre.getValueSet();
					}else{
						IterationCalculation iterCal=pre.getIterationCal();
						List<VexNode> loopList=getLoopNodes(pre,n);
						while(iterCal!=null && iterCal.isIterationOver())
						{
							//如果迭代时区间发生变化，则继续用widening进行迭代
							for(VexNode vex : loopList)
							{
								//在迭代尚不稳定时，每次先清空循环内节点和边的contradict标识
								vex.setContradict(false);
								for(Edge e : vex.getOutedges().values())
									e.setContradict(false);
								visit(vex,data);
							}
						}
						if(iterCal instanceof WideningCalculation && !iterCal.calculateOver){
							//如果迭代后区间不变，则进行narrowing迭代
							Domain wideningDomain=iterCal.lastDomain;
							VarDomainSet wideningVar=new VarDomainSet(iterCal.lastVarDomainSet);
							iterCal.clear();
							iterCal=new NarrowingCalculation();
							iterCal.setLastDomain(wideningDomain);
							iterCal.setLastVarDomainSet(wideningVar);
							pre.setIterationCal(iterCal);
							
							while(iterCal.isIterationOver())
							{
								for(VexNode vex : loopList)
								{
									//在迭代尚不稳定时，每次先清空循环内节点和边的contradict标识
									vex.setContradict(false);
									for(Edge e : vex.getOutedges().values())
										e.setContradict(false);
									visit(vex,data);
								}
							}
							iterCal.clear();
						}
					}
				}
				ConditionData condata = pre.getCondata();
				if (condata != null) {
					SymbolDomainSet ds = condata.getFalseMayDomainSet();
					if (pre.getName().startsWith("while_head") || pre.getName().startsWith("for_head") || pre.getName().startsWith("do_while_out1")) {
						if(!Config.LOOPCAL||looplayer > Config.LOOPLAYER){
							SymbolDomainSet old=pre.getSymDomainset();
							pre.setSymDomainset(null);
							ds=condata.getFalseMayDomainSet();
							pre.setSymDomainset(old);
						}else{
							valueset=pre.getValueSet();
							domainset=pre.getSymDomainset();
						}
						domainset=SymbolDomainSet.union(SymbolDomainSet.intersect(domainset, ds), ds);
					} else {
						domainset=SymbolDomainSet.intersect(domainset, ds);
					}
					if(domainset.isContradict()){
						edge.setContradict(true);
						//zys:2010.4.23
						continue;
					}else{
						n.mergeValueSet(valueset,domainset);
					}		
				}else{
					n.mergeValueSet(valueset,domainset);
				}
			}else if (n.getName().startsWith("label_head_default")) {
				//default分支处，应该获取所有case分支的合并区间，与switch中变量的总区间取差值
				if(pre.getName().startsWith("switch_head")){
					defaultDomain(pre,n);
					domainset=n.getSymDomainset();
					SymbolDomainSet ds=pre.getSymDomainset();
					domainset=SymbolDomainSet.union(SymbolDomainSet.intersect(domainset, ds), ds);
					n.mergeValueSet(valueset,domainset);
					n.removeUnusedSymbols();
					continue;
				}
			}else{
				n.mergeValueSet(valueset,domainset);
			}
			n.mergeSymbolDomainSet(domainset);
		}

		boolean b = !n.getInedges().isEmpty();
		for(Edge edge:list){
			if (n.getName().startsWith("while_head") || n.getName().startsWith("for_head")||n.getName().startsWith("do_while_head")) {
				//对于for和While语句 do-while语句只检查第一条入边
				if(edge.getContradict()){
					break;
				}
			}
			if (!edge.getContradict()) {
				b = false;
				break;
			}
		}
		//该节点矛盾，不可达,设置所有出边的矛盾标志
		if (b || (n.getSymDomainset() != null && n.getSymDomainset().isContradict())) {
			n.setContradict(true);
			for (Edge edge: n.getOutedges().values()) {
				edge.setContradict(true);
			}
			return;
		}
	}
	
	private void calculateOUT(VexNode n ,Object data){
		//在函数头结点，对其中的非指针类型参数进行区间初始化
		if(n.getName().startsWith("func_head")){
			ASTFunctionDefinition temp=(ASTFunctionDefinition) n.getTreenode();
			Set<VariableNameDeclaration> paramList=temp.getScope().getVariableDeclarations().keySet();
			for(VariableNameDeclaration param : paramList)
			{
				CType type=param.getType();
				//防止由于指针类型的参数初始化，导致NPD等的模式误报
				if(type == null || type instanceof CType_Union 
						|| type instanceof CType_Struct || type instanceof CType_Enum)
					continue;
				Domain d=null;
				if(Config.USEUNKNOWN){
					d = Domain.getUnknownDomain(Domain.getDomainTypeFromType(type));
				}else {
					if(type instanceof CType_Pointer)
						continue;//不用unknown时，不初始化指针类型的变量
					d = Domain.getFullDomainFromType(type);	
				}
				SymbolFactor sym = SymbolFactor.genSymbol(type, param.getImage());
				Expression expr = new Expression(sym);
				n.addSymbolDomain(sym, d);
				n.addValue(param, expr);
			}
			return;
		}
		// 计算新的值
		SimpleNode treenode = n.getTreenode();
		ExpressionVistorData exprdata = new ExpressionVistorData();
		exprdata.currentvex=n;
		exprdata.sideeffect=true;
		ExpressionValueVisitor exprvisitor = new ExpressionValueVisitor();
		ConditionData condata = new ConditionData(n);
		ConditionDomainVisitor convisitor = new ConditionDomainVisitor();
		if (!n.isBackNode()) {
			// 条件分支可能：if do while for switch
			if (n.getName().startsWith("if_head_")) {
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
				treenode.jjtGetChild(0).jjtAccept(convisitor, condata);
				n.setCondata(condata);
			} else if (n.getName().startsWith("assert_")) {
				treenode.getFirstChildInstanceofType(ASTConditionalExpression.class).jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
				treenode.getFirstChildInstanceofType(ASTConditionalExpression.class).jjtGetChild(0).jjtAccept(convisitor, condata);
				n.setCondata(condata);
			} else if (n.getName().startsWith("decl_stmt_")
						|| n.getName().startsWith("for_init_")
						|| n.getName().startsWith("for_inc_")
						|| n.getName().startsWith("return_")
						|| n.getName().startsWith("stmt_")) {
				treenode.jjtAccept(exprvisitor, exprdata);
			} else if (n.getName().startsWith("switch_head_")) {
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
			} else if (n.getName().startsWith("label_head_case")) {
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
				caseDomain(n,exprdata,exprvisitor);
			} else if (n.getName().startsWith("switch_out_")){
				//switch_out时，取得所有前驱节点的结果进行合并
				switchOutDomain(n);
			}else if (n.getName().startsWith("for_head_")) {
				/**dongyk 20120306 将节点设置为是循环头节点标志*/
				Node con=null;
				if(treenode.forChild[1]){
					if(treenode.forChild[0]){
						con=treenode.jjtGetChild(1);
					}else{
						con=treenode.jjtGetChild(0);
					}
				}
				if(con!=null){
					con.jjtAccept(exprvisitor, exprdata);
					iterationCalculate(n,condata,convisitor,con);
				}
			} else if (n.getName().startsWith("do_while_out1_")) {
				/**dongyk 20120306 将节点设置为是循环头节点标志*/
			//	n.setLoopHead(true);
				treenode.jjtAccept(exprvisitor, exprdata);
				iterationCalculate(n, condata, convisitor, treenode);
			} else if (n.getName().startsWith("while_head_")) {
				/**dongyk 20120306 将节点设置为是循环头节点标志*/
			//	n.setLoopHead(true);
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
				iterationCalculate(n, condata, convisitor, treenode.jjtGetChild(0));
			} 
		}else if (n.getName().startsWith("func_out")){
			//如果存在return 语句，则计算函数返回值
			MethodNameDeclaration mnd=((ASTFunctionDefinition)treenode).getDecl();
			Method method=mnd.getMethod();
			for(Edge e:n.getInedges().values()){
				if(method==null)
					break;
				if(e.getContradict()){
					continue;
				}
				VexNode v=e.getTailNode();
				if (v.getTreenode() instanceof ASTJumpStatement && v.getTreenode().getImage().equals("return")) {
					if(v.getTreenode().jjtGetNumChildren() == 0)//liuli:对于没有返回值的return语句则直接跳过
						continue;
					ASTExpression expr=(ASTExpression) v.getTreenode().jjtGetChild(0);
					exprdata.currentvex = v;
					expr.jjtAccept(exprvisitor, exprdata);
					//zys:2010.8.12	如果return 语句计算不出来，则按照函数返回值类型创建一个该类型的全值区间
					if(exprdata.value==null){
						CType type=method.getReturnType();
						Domain d;
						if(Config.USEUNKNOWN)
							d = Domain.getUnknownDomain(Domain.getDomainTypeFromType(type));
						else	
							d = Domain.getFullDomainFromType(type);
						method.addReturnValue(d);
						break;
					}
					//zys:2010.7.21
					Domain d=exprdata.value.getDomain(exprdata.currentvex.getSymDomainset());
//					Domain d=exprdata.value.getDomain(v.getSymDomainset());
					//函数返回值处理 ssj
					if(d == null){
//						CType type=method.getReturnType();		
//            			if(type!=null && type instanceof CType_Pointer){
//            				String str = "NULL";
//            				PointerDomain pdomain = PointerDomain.valueOf(str);
//            				method.addReturnValue(pdomain);
//            			}else{
//            				continue;
//            			}
					}else if(d.getDomaintype() == DomainType.POINTER){
						if(method.getReturnDomain() != null && method.getReturnDomain().getDomaintype() == DomainType.POINTER){
							Domain pdomain = Domain.union(d, method.getReturnDomain(), method.getReturnType());
							method.addReturnValue(pdomain);
						}else if(method.getReturnDomain() == null){
							method.addReturnValue(d);
						}
						PointerDomain pd = (PointerDomain)d;
						HashSet<CType_AllocType> Type = pd.Type;
						if(Type.contains(CType_AllocType.heapType)){
							method.setIsAllocate(true);
						}
					}
					else if(method != null && d != null && d.getDomaintype() != DomainType.POINTER){//liuli:区间d为空的时候不加入
						method.addReturnValue(Domain.union(d, method.getReturnDomain(), method.getReturnType()));
					}		
				}
			}
			if(Config.INTER_METHOD_TRACE)
			{
				if (method != null) 
				{
					System.err.println("Method Return Domain : " + method + " = " + method.getReturnDomain());
				}
			}
			if (Config.USE_SUMMARY) 
			{
				//计算函数摘要
				InterContext.cntMethodFeture(n);
			}
			
		}
		n.removeUnusedSymbols();

		if (n.getSymDomainset() != null && n.getSymDomainset().isEmpty()) {
			//n.setSymDomainset(null);
		}
	}

	/** 对节点进行访问 */
	public void visit(VexNode n, Object data) {
		// 由前驱节点的domain求当前节点domain
		n.setVisited(true);
		calculateIN(n, data);
		
		//设置当前节点的lastvardomainset
		if(n.getValueSet()==null){
			n.setLastvalueset(null);
		}else{
			ValueSet vs=new ValueSet(n.getValueSet());
			n.setLastvalueset(vs);
		}
		if(n.getSymDomainset()==null){
			n.setLastsymboldomainset(null);
		}else{
			n.setLastsymboldomainset(new SymbolDomainSet(n.getSymDomainset()));
		}
		
		//防止循环迭代时发生死循环
		if(n.getIterationCal()!=null || !n.getContradict()){
			calculateOUT(n,data);
		}
		
		lastVexNodeNumber=getNodeNum(n);		
	}

	/** 对边进行访问 */
	public void visit(Edge e, Object data) {

	}

	/** 对图进行访问 */
	public void visit(Graph g, Object data) {

	}
	
	private int getNodeNum(VexNode n)
	{
		int index=n.getName().lastIndexOf("_");
		String num=n.getName();
		num=n.getName().substring(index+1);
		return Integer.parseInt(num);
	}

	/** 判断node节点是否为单独变量或常数 */
	private boolean isSingleChild(SimpleNode node){
		while(node.jjtGetNumChildren() == 1){
			if((node.jjtGetChild(0) instanceof ASTPrimaryExpression)){
				return true;				
			}
			node = (SimpleNode) node.jjtGetChild(0);
		}
		return false;
	}
	
	public static void iterationCalculate(VexNode n, ConditionData condata, ConditionDomainVisitor convisitor, Node con) {
		if(Config.LOOPCAL && DomainVexVisitor.looplayer <= Config.LOOPLAYER)
		{
			IterationCalculation iterCal=null;
			if(n.getIterationCal()==null)
			{
				iterCal=new WideningCalculation();
				n.setIterationCal(iterCal);
			}else{
				iterCal=n.getIterationCal();
			}
			iterCal.iterationExec(n);
			condata=ConditionData.calLoopCondtion(condata,n,convisitor, con);
			n.setCondata(condata);
			
		}else{
			condata=ConditionData.calLoopCondtion(condata,n,convisitor,con);
			n.setCondata(condata);
		}
	}
	/** 在switch_out节点，将所有前驱的Case分支中的区间进行合并*/
	private void switchOutDomain(VexNode n) {
		ValueSet oldvalueset=n.getValueSet();
		SymbolDomainSet oldsymset=n.getSymDomainset();
		
		List<Edge> list = new ArrayList<Edge>();
		for (Enumeration<Edge> e = n.getInedges().elements(); e.hasMoreElements();) {
			list.add(e.nextElement());
		}
		Collections.sort(list);

		for (Edge edge : list) {
			VexNode pre = edge.getTailNode();
			SymbolDomainSet domainset=pre.getSymDomainset();

			// 判断分支是否矛盾
			if (edge.getContradict()) {
				continue;
			}
			oldsymset=SymbolDomainSet.intersect(oldsymset, domainset);
			oldsymset=SymbolDomainSet.union(oldsymset, domainset);
			n.mergeValueSet(oldvalueset, oldsymset);
		}
	}
	
	/** 首先判断switch_head中条件变量是否为常量：
	 * １、如果条件变量为常量，则将当前case分支中的区间与其比较，如果一致，则将其他case分支设置为矛盾；
	 * ２、如果为变量，则将当前case分支中的变量区间设置为当前区间*/
	private void caseDomain(VexNode n, ExpressionVistorData exprdata, ExpressionValueVisitor exprvisitor)
	{
		Expression caseValue=exprdata.value;
		//case (0x08 | 0x02 | 0x01):
		//case 0x1;
		//case (0xffffff<<2):
		if(caseValue==null)
			return;
		//zys:2010.8.4	取得switch(n)中的变量，并将其值赋为case i:中i的值
		Expression switchHeadValue = null;
		Expression exp =null;//switch中变量与case中变量的运算结果值
		VexNode pre=null;
		Edge inEdge=null;
		for(Edge e : n.getInedges().values())
		{
			pre=e.getTailNode();
			if(pre.getName().startsWith("switch_head")){
				inEdge=e;
				break;
			}
		}
		
		if(pre.getTreenode().jjtGetNumChildren()==0||inEdge==null)
		{
			return;
		}
		SimpleNode expnode = (SimpleNode) pre.getTreenode().jjtGetChild(0);
		
		if(!isSingleChild(expnode))
			return;
		
		//1、首先判断switch(n)中n为常量的情况
		ASTConstant con = (ASTConstant) (expnode.getSingleChildofType(ASTConstant.class));
		if(con!=null){
			((SimpleNode) pre.getTreenode().jjtGetChild(0)).jjtAccept(exprvisitor, exprdata);						
			switchHeadValue=exprdata.value;
			
			exp =switchHeadValue.sub(caseValue);
			if(exp.getSingleFactor() instanceof NumberFactor){
				NumberFactor f=(NumberFactor)exp.getSingleFactor();
				if(f.getDoubleValue()==0){
					//liuli：2010.5.7如果当前边确定为真分支，则将其父节点的其他出边均设为不可达
					for (Edge edge1: pre.getOutedges().values()) {
						if(!edge1.toString().equals(inEdge.toString()))
							edge1.setContradict(true);
					}
				}else{
					inEdge.setContradict(true);
				}
			}
		}else{
		//2、如果switch(n)中为变量
			ASTPrimaryExpression name = (ASTPrimaryExpression) (expnode.getSingleChildofType(ASTPrimaryExpression.class));
			VariableNameDeclaration v=null;
			if(!name.isMethod()){ //switch参数为变量的情况
				v=name.getVariableDecl(); 
				if(v == null && name.jjtGetNumChildren()>0){							
					SimpleNode cast = (SimpleNode)name.jjtGetChild(0);
					name  = (ASTPrimaryExpression)cast.getSingleOrCastChildofType(ASTPrimaryExpression.class);
					if(name==null || name.getVariableDecl()==null)
						return;
					v=name.getVariableDecl(); 
				}
				switchHeadValue=pre.getValue(v);
				if(switchHeadValue==null)
					return;
			}else{
				//目前将其识别为了函数：switch ((*__errno_location ()))
				return;
			}
			exp =switchHeadValue.sub(caseValue);
			if(exp.getSingleFactor() instanceof NumberFactor){
				NumberFactor f=(NumberFactor)exp.getSingleFactor();
				if(f.getDoubleValue()==0){
					//liuli：2010.5.7如果当前边确定为真分支，则将其父节点的其他出边均设为不可达
					for (Edge edge1: pre.getOutedges().values()) {
						if(!edge1.toString().equals(inEdge.toString()))
							edge1.setContradict(true);
					}
				}else{
					inEdge.setContradict(true);
				}
			}else{
				Domain d=caseValue.getDomain(n.getSymDomainset());
				if(d==null || Domain.isEmpty(d) || d.isUnknown()){
					//zys 2011.6.25	case中的区间算不出，例如case X: X为一个枚举常量值
					return;
				}
				if(switchHeadValue.isComplicated()){
					//zys 2011.6.21: 如果switch(n)中变量的符号表达式比较复杂，则直接为其生成新的符号表达式
					SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
					Expression expr=new Expression(s);
					n.addValue(v, expr);
					n.addSymbolDomain(s, d);
				}else{
					//ZYS 2011.6.21	目前只能处理x=Y+n这种简单的符号表达式，当然理论上也可以处理x=m*Y+n这种类型，但暂时未作处理
					SymbolFactor s=null;
					Domain caseDomain=null;
					if(exp.getTerms().size()==1){
						s=(SymbolFactor) exp.getSingleFactor();
						caseDomain=Domain.castToType(new IntegerDomain(0,0), v.getType());
					}else if(exp.getTerms().size()==2){
						s=(SymbolFactor) exp.getTerms().get(1).getSingleFactor();
						if(s==null)//zys 2011.6.25	case中的区间算不出，例如case X: X为一个枚举常量值
							return;
						Expression temp=new Expression(s).sub(exp);
						caseDomain=temp.getDomain(n.getSymDomainset());
					}
					n.addSymbolDomain(s, caseDomain);
				}
			}
		}
	}
	
	/**首先取出所有的case分支中条件变量的区间，将各区间进行合并然后取反，最终与switch_head头结点中的变量区间取交集 */
	private void defaultDomain(VexNode pre,VexNode n){
		ExpressionVistorData exprdata = new ExpressionVistorData();
		exprdata.currentvex=n;
		exprdata.sideeffect=true;
		ExpressionValueVisitor exprvisitor = new ExpressionValueVisitor();
		Domain caseDomainSet = null,switchHeadDomain = null;
		SimpleNode expnode = (SimpleNode) pre.getTreenode().jjtGetChild(0);
		ASTPrimaryExpression name = (ASTPrimaryExpression) (expnode.getSingleChildofType(ASTPrimaryExpression.class));
		if (name == null || name.isMethod())
			return;
		VariableNameDeclaration v=name.getVariableDecl();
		if(v == null && name.jjtGetNumChildren()>0){							
			SimpleNode cast = (SimpleNode)name.jjtGetChild(0);
			name  = (ASTPrimaryExpression)cast.getSingleOrCastChildofType(ASTPrimaryExpression.class);
			if(name==null || name.getVariableDecl()==null)
				return;
			v=name.getVariableDecl(); 
		}
		
		//先计算出所有case语句的区间，并取反
		for (Edge edge : pre.getOutedges().values()) {
			VexNode head = edge.getHeadNode();
			if(head.getName().startsWith("label_head_case_")){
				((SimpleNode) head.getTreenode().jjtGetChild(0)).jjtAccept(exprvisitor, exprdata);
				Expression e = exprdata.value;
				if(e==null)
					continue;
				Domain dm = e.getDomain(head.getSymDomainset());
				if(dm != null){
					caseDomainSet = Domain.union(caseDomainSet, dm, v.getType());	
				}  							
			}
		}
		caseDomainSet = Domain.inverse(caseDomainSet);
		
		//然后计算出switch头结点变量的区间，与上述区间取交
		SymbolFactor s=SymbolFactor.genSymbol(v.getType(),v.getImage());
		Expression exp1=new Expression(s);
		n.addValue(v, exp1);
		switchHeadDomain=pre.getDomain(v);
		if(switchHeadDomain == null){//如果switch头结点的条件变量区间未知
			switchHeadDomain=s.getDomainWithoutNull(n.getSymDomainset());			
			switchHeadDomain = Domain.intersect(switchHeadDomain, caseDomainSet, v.getType());
		}else{
			switchHeadDomain = Domain.intersect(switchHeadDomain, caseDomainSet, v.getType());
		}
		n.addSymbolDomain(s, switchHeadDomain); 
	}
	
	/** 获取控制流图上每个循环所包括的全部结点
	 * 当存在嵌套循环时，正确读取每层循环所包含的所有结点*/
	private List<VexNode> getLoopNodes(VexNode loopHead,VexNode loopTail)
	{
		List<VexNode> list=new ArrayList<VexNode>();
		
		Graph g=loopHead.getGraph();
		ArrayList<VexNode> listnodes=new ArrayList<VexNode>();
		listnodes.addAll(g.nodes.values());
		Collections.sort(listnodes);
		boolean b=false;
		if(loopHead.getName().startsWith("do_while_out1"))
		{//对do-while循环而言，它的do_while_out1节点为loopHead节点，do_while_out2节点为loopTail节点
			for(VexNode v : listnodes)
			{
				if(b==true){
					if(!v.equals(loopTail)){
						list.add(v);
					}else{
						break;
					}
				}else{
					//取do_while_out1节点的真分支，即为其do_while_head节点
					Edge trueEdge=null;
					for(Edge vex : loopHead.getOutedges().values()){
						if(vex.getName().startsWith("T_")){
							trueEdge=vex;
							break;
						}
					}
					VexNode temp=trueEdge.getHeadNode();
					if(v.equals(temp))
					{
						list.add(v);
						b=true;
					}else{
						continue;
					}
				}
			}
		}else{
			for(VexNode v : listnodes)
			{
				if(b==true){
					if(!v.equals(loopTail) && !v.equals(loopTail)){
						list.add(v);
					}else{
						break;
					}
				}else{
					if(v.equals(loopHead))
					{
						list.add(v);
						b=true;
					}else{
						continue;
					}
				}
			}
		}
		return list;
	}
}
