package softtest.cfg.c;

import softtest.DefUseAnalysis.c.*;
import softtest.ast.c.*;
import softtest.domain.c.analysis.*;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.fsm.c.*;
import softtest.fsmanalysis.c.Report;
import softtest.symboltable.c.Type.*;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.VariableNameDeclaration;

import java.util.*;



/** 图的顶点类 */
public class VexNode extends Element implements Comparable<VexNode> {
	/**zys:2010.5.17	处理循环时循环头节点如while_head,for_head,do_while_out1所关联的
	 * widening或narrowing算子*/
	IterationCalculation iterationCal=null;
	
	/** 能够到达当前节点的变量定义出现 */
	LiveDefsSet liveDefs = new LiveDefsSet();
	
	/** 名称 */
	String name;

	/** 入边集合 */
	Hashtable<String, Edge> inedges = new Hashtable<String, Edge>();

	/** 出边集合 */
	Hashtable<String, Edge> outedges = new Hashtable<String, Edge>();
	
	/** 节点对应的抽象语法树节点 */
	SimpleNode treenode = null;

	/** 真分支标志 */
	public boolean truetag = false;

	/** 假分支标志 */
	public boolean falsetag = false;

	/** 访问标志 */
	boolean visited = false;

	/** 用于比较的数字 */
	int snumber = 0;

	/** 该节点是否矛盾标志，用于控制流图中的不可达路径 */
	boolean contradict = false;
	
	/** 是否是循环头节点标志*/
	boolean loopHead = false;
	/** 是循环头节点，循环中的循环体是否能至少执行一次*/
	boolean loopExecuteAtleastOnce=false;
	
	private Graph graph=null;
	
	transient ValueSet valueset=new ValueSet();
	
	transient SymbolDomainSet symboldomainset=new SymbolDomainSet();
	
	/**zys:2010.5.10 在故障模式分析时，获取上一节点的符号取值信息 */
	transient ValueSet lastvalueset;
	transient SymbolDomainSet lastsymboldomainset;
	
	transient VarDomainSet varDomainSet;
	/** 节点上的变量出现集合 */
	ArrayList<NameOccurrence> occs=new ArrayList<NameOccurrence>();

	//zys
	/** 状态机实例集合 */
	transient FSMMachineInstanceSet fsminstanceset = new FSMMachineInstanceSet();
	
	/** 条件限定域集 */
	transient ConditionData condata = null;

	/**zys:如果是故障模式计算，则通过lastvalueset计算 */
	private boolean fsmCompute=false;

	public boolean isFsmCompute() {
		return fsmCompute;
	}

	public void setfsmCompute(boolean fsmCompute){
		this.fsmCompute=fsmCompute;
	}
	
	/** 获得状态机实例集合 */
	public FSMMachineInstanceSet getFSMMachineInstanceSet() {
		return fsminstanceset;
	}

	/** 设置状态机实例集合 */
	public void setFSMMachineInstanceSet(FSMMachineInstanceSet fsminstanceset) {
		this.fsminstanceset = fsminstanceset;
	}
	
	/** 删除那些空的状态机	 */
	public void rmFSMMachineInstanceSet(FSMMachineInstance fsminstance) {
		this.fsminstanceset.getTable().remove(fsminstance);
	}
	
	/** 将状态机实例集合set合并到fsminstanceset中 */
	public void mergeFSMMachineInstances(FSMMachineInstanceSet set) {
		fsminstanceset.mergeFSMMachineInstances(set);
	}
	
	public void mergFSMMachineInstancesWithoutConditon(FSMMachineInstanceSet set){
		fsminstanceset.mergFSMMachineInstancesWithoutConditon(set);
	}
	
	/**设置序号数字*/
	public void setSnumber(int snumber){
		this.snumber=snumber;
	}
	
	/**获得序号数字*/
	public int getSnumber(){
		return this.snumber;
	}

	/** 以指定的名字和语法树节点创建控制流图节点 */
	public VexNode(String name, SimpleNode treenode) {
		this.name = name;
		this.treenode = treenode;
		treenode.addVexNode(this);
	}

	/** 控制流图访问者的accept */
	@Override
	public void accept(GraphVisitor visitor, Object data) {
		visitor.visit(this, data);
	}
	
	/** 设置节点访问标志 */
	public void setVisited(boolean visited) {
		this.visited = visited;
	}

	/** 获得节点访问标志 */
	public boolean getVisited() {
		return visited;
	}

	/** 获得节点是否矛盾标志 */
	public boolean getContradict() {
		return contradict;
	}

	/** 设置节点是否矛盾标志 */
	public void setContradict(boolean contradict) {
		this.contradict = contradict;
	}
	
	public boolean isLoopHead(){
		return loopHead;
	}
	
	public void setLoopHead(boolean loopHead){
		this.loopHead=loopHead;
	}
	public boolean getLoopExecuteAtleastOnce(){
		
		return loopExecuteAtleastOnce;
	}
	
	public void setLoopExecuteAtleastOnce(boolean loopExecuteAtleastOnce){
		this.loopExecuteAtleastOnce=loopExecuteAtleastOnce;
	}

	/** 设置节点关联的语法树节点 */
	public void setTreenode(SimpleNode treenode) {
		this.treenode = treenode;
	}

	/** 获得节点关联的语法树节点 */
	public SimpleNode getTreenode() {
		return treenode;
	}

	/** 获得节点名称 */
	public String getName() {
		return name;
	}

	/** 获得入边集合 */
	public Hashtable<String, Edge> getInedges() {
		return inedges;
	}

	/** 获得出边集合 */
	public Hashtable<String, Edge> getOutedges() {
		return outedges;
	}

	/** 比较区间的顺序，用于排序 */
	public int compareTo(VexNode e) {
		if (snumber == e.snumber) {
			return 0;
		} else if (snumber > e.snumber) {
			return 1;
		} else {
			return -1;
		}
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append(""+this.snumber+":");
		sb.append(name);
		return sb.toString();
	}
	
	/** 判断节点是不是语句的末尾节点，如if的out */
	public boolean isBackNode(){
		if(name.startsWith("if_out")||name.startsWith("while_out")
		||name.startsWith("for_out")||name.startsWith("switch_out")
		||name.startsWith("do_while_out2")||name.startsWith("func_out")){
			return true;
		}
		return false;
	}	
	
	/**
	 * 查找当前节点到下一个节点之间的边
	 * @param head 指定的下一个节点
	 * @return 当前节点到下一个节点如果存在一条边，则返回改变，否则返回null
	 */
	public Edge getEdgeByHead(VexNode head){
		for(Edge e:outedges.values()){
			if(e.headnode==head){
				return e;
			}
		}
		return null;
	}

	public Graph getGraph() {
		return graph;
	}

	public void setGraph(Graph g) {
		this.graph = g;
	}

	public void setName(String name) {
		this.name = name;
	}
	
	/** 获得节点上的变量出现集合 */
	public ArrayList<NameOccurrence> getOccurrences(){
		return occs;
	}
	
	//add by zhouhb
	/** 获得节点上某个变量的出现*/
	public NameOccurrence getVariableNameOccurrence(VariableNameDeclaration decl) {
		for(NameOccurrence occ : occs) {
			if(occ.getDeclaration().equals(decl))
				return occ;
		}
		return null;
	}
	
	/** 获得节点到达定义集合，即获得能够到达当前节点的变量定义出现的集合 */
	public LiveDefsSet getLiveDefs(){
		return liveDefs;
	}
	
	public ValueSet getValueSet() {
		return valueset;
	}

	public void setValueSet(ValueSet abstractvalues) {
		this.valueset = abstractvalues;
	}
	
	/** 修改变量v的抽象取值 */
	public Expression addValue(VariableNameDeclaration v, Expression value) {
		if (valueset == null) {
			valueset = new ValueSet();
		}
		return valueset.addValue(v, value);
	}

	/** 返回变量v的抽象取值，如果变量v不属于节点关联的域集则返回null */
	public Expression getValue(VariableNameDeclaration v) {
		//如果是模式计算阶段：
		if(fsmCompute){
			if (lastvalueset == null||v==null) {
				return null;
			} else {
				Expression e=lastvalueset.getValue(v);
				if(e!=null)
					return e;
			}
		}
		if (valueset == null||v==null) {
			return null;
		} else {
			return valueset.getValue(v);
		}
	}
	
	public Domain getDomain(VariableNameDeclaration v) {
		Domain ret=null;
		Expression e=getValue(v);
		if(e!=null){
			if(fsmCompute){
				ret= e.getDomain(lastsymboldomainset);
			}else{
				ret= e.getDomain(symboldomainset);
			}
			CType type=v.getType();
			if(type!=null){
				ret=Domain.castToType(ret, type);
			}
		}
		return ret;
	}	
	
	
	public ConditionData getCondata() {
		return condata;
	}

	public void setCondata(ConditionData condata) {
		this.condata = condata;
	}
/**
	public void clear() {
		inedges.clear();
		outedges.clear();
		if(fsminstanceset!=null){
			//System.err.println(name+"节点状态机实例集合未清空？");
			fsminstanceset.clear();
			//fsminstanceset=null;
		}
		liveDefs.clear();
		occs.clear();
		//treenode = null;	
		valueset.clearValueSet();
		if(symboldomainset!=null)
			symboldomainset.clearDomainSet();
		if(condata!=null)
			condata.clearDomains();
		if(iterationCal!=null){
			iterationCal.clear();
		}
		if(lastvalueset!=null)
			lastvalueset.clearValueSet();
		if(lastsymboldomainset!=null)
			lastsymboldomainset.clearDomainSet();
		if(varDomainSet!=null)
			varDomainSet.clearDomainSet();
	}
*/	
	//modify by JJL,2016-1-25
	public void clear() {
		if(fsminstanceset!=null){
			fsminstanceset.clear();
		}
	}
	
	public SymbolDomainSet getSymDomainset() {
		return symboldomainset;
	}

	public void setSymDomainset(SymbolDomainSet oldset) {
		this.symboldomainset = oldset;
	}
	
	public Domain getSymbolDomain(SymbolFactor s){
		if(symboldomainset==null){
			return null;
		}
		return symboldomainset.getDomain(s);
	}
	
	public void addSymbolDomain(SymbolFactor s,Domain domain){
		if(domain==null){
			return;
		}
		if(symboldomainset==null){
			symboldomainset=new SymbolDomainSet();
		}
		symboldomainset.addDomain(s, domain);
	}
	
	public void mergeSymbolDomainSet(SymbolDomainSet ds){
		symboldomainset=SymbolDomainSet.union(symboldomainset, ds);
	}
	
	public void mergeValueSet(ValueSet vs,SymbolDomainSet ds){
		//zys:2010.9.16	循环头节点的区间合并需要特殊处理，如果循环的入边中函数参数未初始化，而回边中相应变量经过运算后
		//得到某中间结果，合并时会丢失入边的区间（此时入边的区间应该是各变量区间类型的全集），导致错误
		if (name.startsWith("while_head") || name.startsWith("for_head") || name.startsWith("do_while_out1")
				|| name.startsWith("if_out") || name.startsWith("switch_out")) 
		{
			//2、获取循环入边节点之前已经声明但没有初始化的变量，将其区间初始化为全区间
			Set<VariableNameDeclaration> localVarList=getTreenode().getScope().getParent().getVariableDeclarations().keySet();
			for(VariableNameDeclaration localVar : localVarList)
			{
				CType type=localVar.getType();
				//防止由于指针类型的参数初始化，导致NPD等的模式误报
				if(type==null || type instanceof CType_AbstPointer || type instanceof CType_Union 
						|| type instanceof CType_Struct || type instanceof CType_Enum)
					continue;
				
				//防止对循环之后声明的变量进行区间初始化
				int location=localVar.getNode().getBeginFileLine();
				int thisLocation=treenode.getBeginFileLine();
				if(location>thisLocation)
					continue;
				Expression expr=vs.getValue(localVar);
				if(expr==null){
					SymbolFactor sym=SymbolFactor.genSymbol(type, localVar.getImage());
					Domain d=Domain.getFullDomainFromType(type);
					expr=new Expression(sym);
					ds.addDomain(sym, d);
					vs.addValue(localVar, expr);
				}
			}
		}
		
		ValueSet newset=new ValueSet();
		
		Expression value1 = null,value2=null;
		Hashtable<VariableNameDeclaration,Expression> table=valueset.getTable();
		for(VariableNameDeclaration v: table.keySet())
		{
			value1=table.get(v);
			value2=vs.getValue(v);
			CType type=v.getType();
			
			if(value2==null || value1.equals(value2)){
				newset.addValue(v, value1);
			}else{
				SymbolFactor sym=SymbolFactor.genSymbol(type,v.getImage());
				addSymbolDomain(sym, Domain.union(value1.getDomain(symboldomainset), value2.getDomain(ds), type));
				newset.addValue(v, new Expression(sym));
			}
		}
		
		table=vs.getTable();
		for(VariableNameDeclaration v : table.keySet()) {
			value2 =table.get(v);
			value1=valueset.getValue(v);
									
			if(value1==null){
				newset.addValue(v, value2);
				mergeSymbolDomainSet(ds);
			}			
		}
		
		valueset=newset;
		//移除那些超出当前控制流节点作用域的变量
		valueset.removeOutScopeVar(this);
	}
	
	public VarDomainSet getVarDomainSet(){
		if(varDomainSet==null)
			varDomainSet=new VarDomainSet();
		else
			varDomainSet.clearDomainSet();

		Hashtable<VariableNameDeclaration,Expression> table=valueset.getTable();
		for(VariableNameDeclaration v: table.keySet())
		{
			Expression value=table.get(v);
			Domain domain=value.getDomain(symboldomainset);
			CType type=v.getType();
			if(domain!=null){
				if(type!=null&&!(type instanceof CType_Pointer)&&!(type instanceof CType_Array)){
					domain=Domain.castToType(domain, type);
				}
				varDomainSet.addDomain(v, domain);
			}
		}
		return varDomainSet;
	}
	
	public void setVarDomainSet(VarDomainSet varDomainSet) {
		this.varDomainSet = varDomainSet;
	}
	
	public void removeUnusedSymbols(){
		if(symboldomainset==null){
			return;
		}
		HashSet<SymbolFactor> syms=valueset.getAllSymbol();
		ArrayList<SymbolFactor> toremove=new ArrayList<SymbolFactor>();
		for(SymbolFactor s : symboldomainset.getTable().keySet())
		{
			if(!syms.contains(s)){
				toremove.add(s);
			}
		}
		for(SymbolFactor sym:toremove){
			symboldomainset.getTable().remove(sym);
		}
	}

	public ValueSet getLastvalueset() {
		return lastvalueset;
	}

	public void setLastvalueset(ValueSet lastvalueset) {
		this.lastvalueset = lastvalueset;
	}

	public SymbolDomainSet getLastsymboldomainset() {
		return lastsymboldomainset;
	}

	public void setLastsymboldomainset(SymbolDomainSet lastsymboldomainset) {
		this.lastsymboldomainset = lastsymboldomainset;
	}

	public IterationCalculation getIterationCal() {
		return iterationCal;
	}

	public void setIterationCal(IterationCalculation iterationCal) {
		this.iterationCal = iterationCal;
	}
}
