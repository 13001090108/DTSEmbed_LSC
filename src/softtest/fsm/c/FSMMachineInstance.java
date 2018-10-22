package softtest.fsm.c;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.*;

/** 状态机实例，用于跟踪具体状态机，包含多个当前可能状态 */
public class FSMMachineInstance {
	/** 状态机 */
	private FSMMachine fsm = null;

	/** 对应的变量 */
	private VariableNameDeclaration v = null;

	/** 当前可能状态集合 */
	private FSMStateInstanceSet states = null;

	/** 状态机关联的对象 */
	private FSMRelatedCalculation relatedobject = null;

	/** 显示错误时用到的字符串 */
	private String resultstring = "";
	
	/**特定标识开关*/
	private boolean flag = false;//added by zhanghh
	
	/**对应的控制流图*/
	private VexNode releatedVexNode = null;//added by zhanghh	
	
	/**
	 * <p>The state related data used for storing the FSM state informations</p>
	 */
	private Object stateData;
	
	/**是否经过错误状态*/
	private boolean isError = false;//added by xwt  2011.11.3

	/** 对应的抽象语法树上的结点 * */
	SimpleNode relatedASTNode = null;

	/** 构造函数 */
	public FSMMachineInstance() {
		states = new FSMStateInstanceSet();
	}

	/** 拷贝构造函数 */
	public FSMMachineInstance(FSMMachineInstance instance) {
		fsm = instance.fsm;
		v = instance.v;
		if (instance.relatedobject != null) {
			relatedobject = instance.relatedobject.copy();
		}
		resultstring = instance.resultstring;
		relatedASTNode = instance.relatedASTNode;
		releatedVexNode = instance.releatedVexNode;
		
		nodeUseToFindPosition = instance.nodeUseToFindPosition;
		states = new FSMStateInstanceSet(instance.states);
		stateData = instance.stateData;
		traceinfo = instance.traceinfo;
		desp = instance.desp;
		isError = instance.isError;
	}
	
	public boolean isErrorReport() {
		return isError;
	}
	
	public void setErrorReport(boolean isError) {
		this.isError = isError;
	}
	/**
	 * <p>Gets the state related data.</p>
	 * 
	 * @return the state related data
	 */
	public Object getStateData() {
		return stateData;
	}
	
	/**
	 * <p>Sets the state related data.</p>
	 * 
	 * @param stateData
	 */
	public void setStateData(Object stateData) {
		this.stateData = stateData;
	}
	
	/** 增加新的状态，考虑条件的融合 */
	public void addStateInstance(FSMStateInstance state) {
		states.addStateInstance(state);
	}

	/** 增加新的状态，考虑条件的融合 */
	public void addStateInstanceWithoutConditon(FSMStateInstance state) {
		states.addStateInstanceWithoutConditon(state);
	}
	
	/** 设置状态集合 */
	public void setStates(FSMStateInstanceSet states) {
		this.states = states;
	}

	/** 获得状态集合 */
	public FSMStateInstanceSet getStates() {
		return states;
	}

	/** 设置结果字符串 */
	public void setResultString(String resultstring) {
		this.resultstring = resultstring;
	}

	/** 获得结果字符串 */
	public String getResultString() {
		if (resultstring == null || resultstring.trim().length() ==0 ) {
			if (v != null) {
				return v.getImage();
			}
		} else {
			return resultstring;
		}
		return "";
	}

	/** 创建一个开始状态实例 */
	public FSMStateInstance createStartStateInstance() {
		FSMState start = fsm.getStartState();
		if (start == null) {
			throw new RuntimeException("The fsm does not have a start state.");
		}
		return new FSMStateInstance(start);
	}

	/** 设置状态机 */
	public void setFSMMachine(FSMMachine fsm) {
		this.fsm = fsm;
	}

	/** 获得状态机 */
	public FSMMachine getFSMMachine() {
		return fsm;
	}
	/** 变量字符串 */
	//added by cmershen 2016.3.21
	//有时IP会报不出变量，尝试加以修正。
	private String varImage;
	
	public String getVarImage() {
		return varImage;
	}

	public void setVarImage(String varImage) {
		this.varImage = varImage;
	}

	/** 设置相关变量 */
	public void setRelatedVariable(VariableNameDeclaration v) {
		if (fsm.isVariableRelated()) {
			this.v = v;
		} else {
			throw new RuntimeException(
					"Try to assign a variable to a nonvariableRelated statemachine.");
		}
	}

	/** 获得相关变量 */
	public VariableNameDeclaration getRelatedVariable() {
		return v;
	}

	/** 设置相关对象 */
	public void setRelatedObject(FSMRelatedCalculation relatedobject) {
		this.relatedobject = relatedobject;
	}

	/** 获得相关对象 */
	public FSMRelatedCalculation getRelatedObject() {
		return relatedobject;
	}

	/** 如果相关对象和变量和状态机相等，则被认为相等 */
	@Override
	public boolean equals(Object o) {
		if ((o == null) || !(o instanceof FSMMachineInstance)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		boolean b = true;
		FSMMachineInstance x = (FSMMachineInstance) o;
		if (stateData != x.stateData) {
			b = false;
		}
		if (relatedobject != null) {
			if (fsm != x.fsm || v != x.v) {
				b = false;
			} else if (fsm == x.fsm && v == x.v) {
				if (!relatedobject.equals(x.relatedobject))
					b = false;
				if (x.relatedASTNode != this.relatedASTNode) {
					b = false;
				}
			}
		} else {
			if (fsm != x.fsm || v != x.v || relatedASTNode != x.relatedASTNode) {
				b = false;
			}
		}
		return b;
	}

	/** 因为状态机实例会被用于作为hashtable的key,为了保证值相等的状态机实例有相同的hashcode，所以重写了该方法 */
	@Override
	public int hashCode() {
		int i = 0;
		if (v != null) {
			i = i + v.hashCode();
		}
		if (relatedobject != null) {
			i = i + relatedobject.hashCode();
		}
		i = i + fsm.hashCode();
		return i;
	}

	/** 打印 */
	@Override
	public String toString() {
		String s = "";
		s = s + fsm + " on " + getResultString() + ":" + states;
		return s;
	}

	/** 根据当前控制流节点，计算状态机的所有状态条件 */
	public void calDomainSet(VexNode vex) {
		states.calDomainSet(vex);
	}

	/** 根据前趋控制流判断节点和是否为真分支标志，计算状态机的所有状态条件 */
	public void calCondition(VexNode pre, boolean istruebranch) {
		states.calCondition(pre, istruebranch);
	}

	/** 根据caselabel节点和switch节点，计算状态机的所有状态条件 */
	public void calSwitch(VexNode n, VexNode pre) {
		states.calSwitch(n, pre);
	}

	// add by ZhangGuanNan
	/** 设置与该状态机实例相关的抽象语法树上的结点* */
	public void setRelatedASTNode(SimpleNode snode) {
		this.relatedASTNode = snode;
	}

	/** 获取与该状态机实例相关的抽象语法树上的结点* */
	public SimpleNode getRelatedASTNode() {
		return this.relatedASTNode;
	}
	
	/** 用来辅助定位具体故障所在地的抽象语法树节点，存放在状态机实例里*/
	public SimpleNode nodeUseToFindPosition;
	
	public void setNodeUseToFindPosition(SimpleNode node){
		this.nodeUseToFindPosition=node;
	}
	public SimpleNode getNodeUseToFindPosition(){
		return this.nodeUseToFindPosition;
	}
	
	/**设置同一文件中不同状态机实例的标识* */
	public int  idFlag;
	public void setFsmIdFlag(int idflag){
		this.idFlag=idflag;
	}
	public int getFsmIdFlag(){
		return idFlag;
	}
	// end by zhanggn
	
	/**设置特定开关*/
	public void setFlag(boolean bool){
		this.flag = bool;
	}
	
	/**获取特定开关*/
	public boolean getFlag(){
		return this.flag;
	}
	
	/**设定相关的控制流节点*/
	public void setReleatedVexNode(VexNode vexNode){
		this.releatedVexNode = vexNode;
	}
	
	/**获取相应的控制流节点*/
	public VexNode getReleatedVexNode(){
		return this.releatedVexNode;
	}
	
	private String traceinfo = "";
	public String getTraceinfo() {
		return traceinfo;
	}

	public void setTraceinfo(String traceinfo) {
		this.traceinfo = traceinfo;
	}
	
	private String desp = "";
	public String getDesp() {
		return desp;
	}
	
	public void setDesp(String desp) {
		this.desp = desp;
	}
}
