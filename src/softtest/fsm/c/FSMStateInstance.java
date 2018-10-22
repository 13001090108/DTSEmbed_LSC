package softtest.fsm.c;

import java.util.Hashtable;

import softtest.ast.c.*;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.analysis.ConditionData;
import softtest.domain.c.analysis.ConditionDomainVisitor;
import softtest.domain.c.analysis.DomainVexVisitor;
import softtest.domain.c.analysis.ExpressionValueVisitor;
import softtest.domain.c.analysis.ExpressionVistorData;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.domain.c.analysis.VarDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.NumberFactor;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_Array;
import softtest.symboltable.c.Type.CType_Pointer;

/** 状态实例 */
public class FSMStateInstance {
	/** 当前状态 */
	private FSMState state = null;

	/** 当前状态关联的条件变量域集 */
	private VarDomainSet vardomainset;
	private ValueSet valueSet=new ValueSet();
	private SymbolDomainSet symbolDomainSet=new SymbolDomainSet();
	/** 以指定状态构造状态实例 */
	public FSMStateInstance(FSMState state) {
		this.state = state;
	}

	/** 产生该状态的控制流节点 */
	private VexNode sitenode = null;

	/** 设置产生该状态的控制流节点 */
	public void setSiteNode(VexNode sitenode) {
		this.sitenode = sitenode;
	}

	/** 获得产生该状态的控制流节点 */
	public VexNode getVexNode() {
		return sitenode;
	}

	/** 拷贝构造函数 */
	public FSMStateInstance(FSMStateInstance instance) {
		this.state = instance.state;
		if(instance.getState().fsm.isPathSensitive()){
			symbolDomainSet=new SymbolDomainSet(instance.symbolDomainSet);
			valueSet=new ValueSet(instance.valueSet);
			vardomainset = getVarDomainSet();
		}
		this.sitenode = instance.sitenode;
	}

	/** 设置当前状态 */
	public void setState(FSMState state) {
		this.state = state;
	}

	/** 获得当前状态 */
	public FSMState getState() {
		return state;
	}

	/** 如果指向的状态相等，则被认为相等 */
	@Override
	public boolean equals(Object o) {
		if ((o == null) || !(o instanceof FSMStateInstance)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		FSMStateInstance x = (FSMStateInstance) o;
		if (state != x.state) {
			return false;
		}
		if(Config.PATH_SENSITIVE==0){
			return true;
		}else{
			//判断当前状态条件是否相同
			if(vardomainset.equals(x.vardomainset))
				return true;
		}
		
		return false;
	}

	/** 用于hash表的key，需要保证值相等则hashcode相等 */
	@Override
	public int hashCode() {
		return state.hashCode();
	}

	/** 打印 */
	@Override
	//zys:待修改
	public String toString() {
		return state.getName() + " =( " + vardomainset + ")  ";
	}
	
	private void updateVarDomainSet(){
		if(vardomainset==null)
			vardomainset=new VarDomainSet();
		else
			vardomainset.clearDomainSet();

		Hashtable<VariableNameDeclaration,Expression> table=valueSet.getTable();
		for(VariableNameDeclaration v: table.keySet())
		{
			Expression value=table.get(v);
			Domain domain=value.getDomain(symbolDomainSet);
			CType type=v.getType();
			if(domain!=null){
				if(type!=null&&!(type instanceof CType_Pointer)&&!(type instanceof CType_Array)){
					domain=Domain.castToType(domain, type);
				}
				vardomainset.addDomain(v, domain);
			}
		}
	}
	
	public VarDomainSet getVarDomainSet(){
		updateVarDomainSet();
		return vardomainset;
	}
	
	/** 根据caselabel节点和switch节点，计算状态的状态条件 */
	public void calSwitch(VexNode n, VexNode pre) {
		ValueSet oldValueSet=pre.getValueSet();
		SymbolDomainSet oldSymbolDomainSet=pre.getSymDomainset();

		// 采用状态条件进行计算，更新状态条件
		pre.setValueSet(valueSet);
		pre.setSymDomainset(symbolDomainSet);
		
		//查询switch(n)中的变量n
		SimpleNode expnode = (SimpleNode) pre.getTreenode().jjtGetChild(0);
		ASTPrimaryExpression pri=(ASTPrimaryExpression) expnode.getSingleChildofType(ASTPrimaryExpression.class);
		if(pri==null || pri.getVariableNameDeclaration()==null)
			return;
		VariableNameDeclaration v=pri.getVariableNameDeclaration();
		
		if(n.getName().startsWith("label_head_case")){
			caseDomain(pre,n,v);
		}else{
			//如果是default分支，则取switch(n)变量n的其他Case分支的反例
			defaultDomain(n,pre,v);
		}
		
		updateVarDomainSet();
		// 恢复原来的域集
		pre.setValueSet(oldValueSet);
		pre.setSymDomainset(oldSymbolDomainSet);
	}

	private void defaultDomain(VexNode n, VexNode pre, VariableNameDeclaration v) {
		Domain caseDomainSet = null,switchHeadDomain = null;
		ExpressionVistorData exprdata = new ExpressionVistorData();
		exprdata.currentvex=n;
		exprdata.sideeffect=true;
		ExpressionValueVisitor exprvisitor = new ExpressionValueVisitor();
		
		//先计算出所有case语句的区间，并取反
		for (Edge edge : pre.getOutedges().values()) {
			VexNode head = edge.getHeadNode();
			if(head.getName().startsWith("label_head_case_")){
				((SimpleNode) head.getTreenode().jjtGetChild(0)).jjtAccept(exprvisitor, exprdata);
				Expression e = exprdata.value;
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
		valueSet.addValue(v, exp1);
		switchHeadDomain=pre.getDomain(v);
		if(switchHeadDomain == null){//如果switch头结点的条件变量区间未知
			switchHeadDomain=s.getDomainWithoutNull(n.getSymDomainset());			
			switchHeadDomain = Domain.intersect(switchHeadDomain, caseDomainSet, v.getType());
		}else{
			switchHeadDomain = Domain.intersect(switchHeadDomain, caseDomainSet, v.getType());
		}
		symbolDomainSet.addDomain(s, switchHeadDomain); 
	}

	/** 根据前趋控制流判断节点和是否为真分支标志，计算状态的状态条件 */
	public void calCondition(VexNode preVex, boolean istruebranch) {
		// 保存域集
		ValueSet oldValueSet=preVex.getValueSet();
		SymbolDomainSet oldSymbolDomainSet=preVex.getSymDomainset();

		// 采用状态条件进行计算，更新状态条件
		preVex.setValueSet(valueSet);
		preVex.setSymDomainset(symbolDomainSet);
		
		SimpleNode treenode = preVex.getTreenode();
		if (treenode == null)
			return;
		if (!preVex.isBackNode()) {
			
			String name = preVex.getName();
			ConditionData condata=new ConditionData(preVex);
			ConditionDomainVisitor convisitor = new ConditionDomainVisitor();
			if (name.startsWith("if_head")) {
				convisitor.visit((ASTExpression) treenode.jjtGetChild(0), condata);
				//preVex.setCondata(condata);
//				condata=preVex.getCondata();
			}else if (name.startsWith("while_head")) {
				DomainVexVisitor.iterationCalculate(preVex, condata, convisitor, treenode.jjtGetChild(0));
			}else if (name.startsWith("for_head")) {
				Node con=null;
				if(treenode.forChild[1]){
					if(treenode.forChild[0]){
						con=treenode.jjtGetChild(1);
					}else{
						con=treenode.jjtGetChild(0);
					}
				}
				if(con!=null)
					DomainVexVisitor.iterationCalculate(preVex, condata, convisitor, con);
			}else if (name.startsWith("do_while_out1")) {
				DomainVexVisitor.iterationCalculate(preVex, condata, convisitor, treenode);
			}
			
			if(condata!=null){
				SymbolDomainSet ds = null;
				if (istruebranch) {
					ds=condata.getTrueMayDomainSet();
					SymbolDomainSet symDomainSet=preVex.getSymDomainset();
					ds=SymbolDomainSet.intersect(symDomainSet, ds);
				} else {
					ds=condata.getFalseMayDomainSet();
					ds=SymbolDomainSet.intersect(preVex.getSymDomainset(), ds);
				}
				symbolDomainSet=ds;
				updateVarDomainSet();
			}
		}
		
		// 恢复原来的域集
		preVex.setValueSet(oldValueSet);
		preVex.setSymDomainset(oldSymbolDomainSet);
	}

	/**zys:2010.7.30 路径敏感状态机分析出错的原因：
	 * 根据当前控制流节点，计算状态的状态条件 */
	public void calDomainSet(VexNode vex) {
		// 保存域集
		ValueSet oldValueSet=vex.getValueSet();
		SymbolDomainSet oldSymbolDomainSet=vex.getSymDomainset();

		// 采用状态条件进行计算，更新状态条件
		vex.setValueSet(valueSet);
		vex.setSymDomainset(symbolDomainSet);
		
		SimpleNode treenode = vex.getTreenode();
		ExpressionVistorData exprdata = new ExpressionVistorData();
		exprdata.currentvex=vex;
		exprdata.sideeffect=true;
		ExpressionValueVisitor exprvisitor = new ExpressionValueVisitor();
		if (treenode.getFirstVexNode() == vex) {
			// 确定是该语法树节点对应的第一个控制流节点
			if(vex.getName().startsWith("if_head")){
//				System.out.println("处理if_head节点,位于："+treenode.getBeginFileLine());
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
			}else if (vex.getName().startsWith("switch_head_")
							|| vex.getName().startsWith("label_head_case_")) {
				treenode.jjtGetChild(0).jjtAccept(exprvisitor, exprdata);
			}else if (vex.getName().startsWith("for_head_") || vex.getName().startsWith("do_while_out1_")
					|| vex.getName().startsWith("while_head_")) {
				if(oldValueSet!=null)
					valueSet=new ValueSet(oldValueSet);
				if(oldSymbolDomainSet!=null)
					symbolDomainSet=new SymbolDomainSet(oldSymbolDomainSet);
			}else {
				treenode.jjtAccept(exprvisitor, exprdata);
			}
		}
//		valueSet=oldValueSet;
//		symbolDomainSet=SymbolDomainSet.union(symbolDomainSet,oldSymbolDomainSet);
		// 去除那些超出作用域的变量
		ValueSet temp = new ValueSet();
		Hashtable<VariableNameDeclaration, Expression> table = valueSet.getTable();
		for (VariableNameDeclaration var : table.keySet()) {
			if (vex.getTreenode().getScope().isSelfOrAncestor(var.getScope())) {
				temp.getTable().put(var, table.get(var));
			}
		}
		valueSet=temp;
		
		updateVarDomainSet();
		
		// 恢复原来的域集
		vex.setValueSet(oldValueSet);
		vex.setSymDomainset(oldSymbolDomainSet);
	}

	public void setVardomainset(VarDomainSet vardomainset) {
		this.vardomainset = vardomainset;
	}

	public ValueSet getValueSet() {
		return valueSet;
	}

	public void setValueSet(ValueSet valueSet) {
		this.valueSet = valueSet;
	}

	public SymbolDomainSet getSymbolDomainSet() {
		return symbolDomainSet;
	}

	public void setSymbolDomainSet(SymbolDomainSet symbolDomainSet) {
		this.symbolDomainSet = symbolDomainSet;
	}

	public void mergeValueSet(ValueSet vs,SymbolDomainSet ds) {
		ValueSet newset=new ValueSet();
		
		Expression value1 = null,value2=null;
		Hashtable<VariableNameDeclaration,Expression> table=valueSet.getTable();
		for(VariableNameDeclaration v: table.keySet())
		{
			value1=table.get(v);
			value2=vs.getValue(v);
			CType type=v.getType();
			
			if(value2==null || value1.equals(value2)){
				newset.addValue(v, value1);
			}else{
				SymbolFactor sym=SymbolFactor.genSymbol(type,v.getImage());
				addSymbolDomain(sym, Domain.union(value1.getDomain(symbolDomainSet), value2.getDomain(ds), type));
				newset.addValue(v, new Expression(sym));
			}
		}
		
		table=vs.getTable();
		for(VariableNameDeclaration v : table.keySet()) {
			value2 =table.get(v);
			value1=valueSet.getValue(v);
									
			if(value1==null){
				newset.addValue(v, value2);
				mergeSymbolDomainSet(ds);
			}			
		}
		
		valueSet=newset;
	}
	
	public void addSymbolDomain(SymbolFactor s,Domain domain){
		if(domain==null){
			return;
		}
		if(symbolDomainSet==null){
			symbolDomainSet=new SymbolDomainSet();
		}
		symbolDomainSet.addDomain(s, domain);
	}
	
	public void mergeSymbolDomainSet(SymbolDomainSet ds){
		symbolDomainSet=SymbolDomainSet.union(symbolDomainSet, ds);
	}
	
	private void caseDomain(VexNode pre, VexNode n, VariableNameDeclaration v)
	{		
		//计算case后常量值
		ASTConstantExpression constantExpression=(ASTConstantExpression)n.getTreenode().jjtGetChild(0);
		ExpressionVistorData exprdata = new ExpressionVistorData();
		exprdata.currentvex=n;
		exprdata.sideeffect=true;
		ExpressionValueVisitor exprvisitor = new ExpressionValueVisitor();
		constantExpression.jjtAccept(exprvisitor, exprdata);
		Expression caseValue=exprdata.value;
		if(caseValue==null)
			return;
		
		//zys:2010.8.4	取得switch(n)中的变量，并将其值赋为case i:中i的值
		Expression switchHeadValue =pre.getValue(v);
		if(switchHeadValue==null)
			return;
		
		Expression exp =switchHeadValue.sub(caseValue);//switch中变量与case中变量的运算结果值
		if(exp.getSingleFactor() instanceof NumberFactor){
			NumberFactor f=(NumberFactor)exp.getSingleFactor();
			if(f.getDoubleValue()==0){
				valueSet.addValue(v, caseValue);
			}
		}else{
			Domain d=caseValue.getDomain(n.getSymDomainset());
			if(d==null)
				return;
			SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
			Expression expr=new Expression(s);
			valueSet.addValue(v, expr);
			symbolDomainSet.addDomain(s, d);
		}
	}
}