package softtest.symboltable.c;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import softtest.ast.c.*;
import softtest.scvp.c.SCVP;
import softtest.scvp.c.SCVPString;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;

public class NameOccurrence implements Serializable
{
	private NameDeclaration decl;
	private SimpleNode location;
	private String image;
	

	
	//zys:
    /** 出现类型 */
    public enum OccurrenceType{
    	/** 定义 */
    	DEF,
    	/** 使用 */
    	USE,
    	DEF_AFTER_USE,//i++;i+=5;
    	//add by cmershen,2016.3.14,函数入口
    	ENTRANCE
    }
    //added by cmershen,2016.5.3 定义点类型
    public enum DefinitionType {
    	ASSIGN,//赋值
    	CONDITION,//条件
    	LOOP,//循环
    	LIB,//库函数
    	PARAMETER,//函数参数
    	FUNCTION//函数副作用
    }
    public String methodName = "";
    /** 出现类型,只针对变量的出现 */
    private OccurrenceType occurrenceType;
    //added by cmershen,2016.5.3 定义点类型
    public DefinitionType definitionType;
    /** 使用-定义链，保存了可以到达本使用出现的所有定义出现，对于定义出现，该链表为null,链表中的元素都为定义出现 */
    private List<NameOccurrence> use_def = null;
    
    /** 定义-使用链，保存了本定义出现所有可以到达的使用出现，对于使用出现，该链表为null,链表中的元素都为使用出现 */
    private List<NameOccurrence> def_use = null;
    
    /** 定义-取消定义链，保存了本定义出现所有可以到达的定义出现，对于使用出现，该链表为null,链表中的元素都为定义出现 */
    private List<NameOccurrence> def_undef = null;
    
    /** 取消定义-定义链，保存了可以到达本定义出现的所有定义出现，对于使用出现，该链表为null,链表中的元素都为定义出现 */
    private List<NameOccurrence> undef_def = null;
    
    //added by cmershen,2016.5.3,增加定值信息列表
   // public List<SCVP> scvpList = null;
    public List<SCVPString> scvpList = null;
    // added by cmershen, 2017.10.30, 增加影响域
    private List<NameOccurrence> effected = new ArrayList<>();
    public SCVPString getSCVP(){
    	if (scvpList != null && scvpList.size() != 0)
    		return scvpList.get(0);
    	return null;
    }
    
	public NameOccurrence(NameDeclaration decl,SimpleNode location, String image)
	{
		this.location = location;
		this.image = image;
		this.decl=decl;
		 //added by cmershen,2016.5.3,增加定值信息列表
		this.scvpList = new ArrayList<SCVPString>();
	}
	
    /** 向定义-取消链添加定义，保证不重复添加 */
    public boolean addDefUndef(NameOccurrence occ){
    	if(occ.getOccurrenceType()==OccurrenceType.DEF || occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE){
    		for(NameOccurrence o:def_undef){
    			if(o.getLocation()==occ.getLocation()){
    				return false;
    			}
    		}
    		def_undef.add(occ);
    		return true;
    	}
    	return false;
    }
    
    /** 向定义-使用链添加定义，保证不重复添加 */
    public boolean addDefUse(NameOccurrence occ){
    	if(occ.getOccurrenceType()==OccurrenceType.USE || occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE){
    		for(NameOccurrence o:def_use){
    			if(o.getLocation()==occ.getLocation()){
    				return false;
    			}
    		}
    		def_use.add(occ);
    		return true;
    	}
    	return false;
    }
    
    /** 向定义-取消链添加定义，保证不重复添加 */
    public boolean addUndefDef(NameOccurrence occ){
    	// modified by cmershen,2016.10.10,添加entrance类型
    	if(occ.getOccurrenceType()==OccurrenceType.DEF || occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE || occ.getOccurrenceType() == OccurrenceType.ENTRANCE){
    		for(NameOccurrence o:undef_def){
    			if(o.getLocation()==occ.getLocation()){
    				return false;
    			}
    		}
    		undef_def.add(occ);
    		return true;
    	}
    	return false;
    }
    
    /** 向使用-定义链添加定义，保证不重复添加 */
    public boolean addUseDef(NameOccurrence occ){ 
    	// modified by cmershen,2016.3.14,添加entrance类型
    	if(occ.getOccurrenceType()==OccurrenceType.DEF || occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE || occ.getOccurrenceType() == OccurrenceType.ENTRANCE){
    		for(NameOccurrence o:use_def){
    			if(o.getLocation()==occ.getLocation()){
    				return false;
    			}
    		}
    		use_def.add(occ);
    		return true;
    	}
    	return false;
    }

	public SimpleNode getLocation()
	{
		return location;
	}

	public boolean equals(Object o)
	{
		NameOccurrence n = (NameOccurrence) o;
		return n.location.equals(location);
	}

	public int hashCode()
	{
		return location.hashCode();
	}

	public String getImage()
	{
		return image;
	}

	public boolean isMethodInvocation(){
		return decl instanceof MethodNameDeclaration;
	}
	
	public String toString()
	{
		return getImage()  + (this.isMethodInvocation() ? "(method call:"+ location.getBeginLine()+")" : ":" + location.getBeginLine());
	}

	public void setImage(String image) {
		this.image = image;
	}

	public void setLocation(SimpleNode location) {
		this.location = location;
	}

	public OccurrenceType getOccurrenceType()
	{
		return occurrenceType;
	}

	public void setOccurrenceType(OccurrenceType occurrenceType)
	{
		this.occurrenceType = occurrenceType;
	}

	public List<NameOccurrence> getUse_def()
	{
		return use_def;
	}

	public void setUse_def(List<NameOccurrence> use_def)
	{
		this.use_def = use_def;
	}

	public List<NameOccurrence> getDef_use()
	{
		return def_use;
	}

	public void setDef_use(List<NameOccurrence> def_use)
	{
		this.def_use = def_use;
	}

	public List<NameOccurrence> getDef_undef()
	{
		return def_undef;
	}

	public void setDef_undef(List<NameOccurrence> def_undef)
	{
		this.def_undef = def_undef;
	}

	public List<NameOccurrence> getUndef_def()
	{
		return undef_def;
	}

	public void setUndef_def(List<NameOccurrence> undef_def)
	{
		this.undef_def = undef_def;
	}
	
	/** 设置声明 */
    public void setDeclaration(NameDeclaration decl){
    	this.decl=decl;
    }
    
    /** 获得声明 */
    public NameDeclaration getDeclaration(){
    	return decl;
    }
    
    /** 检查出现类型 */
    public OccurrenceType checkOccurrenceType(){
    	OccurrenceType type=OccurrenceType.USE;
    	if(isOnLeftHandSide() || isSelfAssignment()){
    		type=OccurrenceType.DEF;
    		if (isSelfAssignment())// || isAssignSameVar(location)) 
    		{
				type = OccurrenceType.DEF_AFTER_USE;
			}
    	}
    	//added by cmershen,2016.3.7
    	//scanf,gets,strcpy,strdup等库函数都看做是定义点！
    	//2016.10.13 cmershen 增加free
    	SimpleNode astNode = this.getLocation();
    	String[] defFuncs = new String[]{"scanf","gets","strcpy","strdup","free"};
    	if(astNode.containsParentOfType(ASTStatement.class)) {
	    	SimpleNode statementAncestor = (SimpleNode) astNode.getFirstParentOfType(ASTStatement.class);
	    	if(statementAncestor.containsChildOfType(ASTPrimaryExpression.class)) {
	    		SimpleNode primaryNode = (SimpleNode) statementAncestor.getFirstChildOfType(ASTPrimaryExpression.class);
	    		if (((ASTPrimaryExpression)primaryNode).isMethod()) { // 该节点是函数调用
	    			String funcName = primaryNode.getImage();
	    			for(String defFunc:defFuncs) {
		    			if(funcName.equals(defFunc)) {
		    				System.out.println(funcName+"函数是定义点，进行修正！");
		    				type = OccurrenceType.DEF;
		    				methodName = funcName;
		    			}
	    			}
	    		}
	    	}
    	}
    	if(type==OccurrenceType.USE){
    		if(use_def==null){
    			use_def=new LinkedList<NameOccurrence>();
    		}
    		def_use=null;
    		def_undef=null;
    		undef_def=null;
    	}else if (type == OccurrenceType.DEF ){
			use_def = null;
			if (def_use == null) {
				def_use = new LinkedList<NameOccurrence>();
			}
			if (def_undef == null) {
				def_undef = new LinkedList<NameOccurrence>();
			}
			if (undef_def == null) {
				undef_def = new LinkedList<NameOccurrence>();
			}
		} else {
			if (use_def == null) {
				use_def = new LinkedList<NameOccurrence>();
			}
			if (def_use == null) {
				def_use = new LinkedList<NameOccurrence>();
			}
			if (def_undef == null) {
				def_undef = new LinkedList<NameOccurrence>();
			}
			if (undef_def == null) {
				undef_def = new LinkedList<NameOccurrence>();
			}
		}
    	return type;
    }
    
    /**
     * @author zys	2010.1.31
     * @return 判断当前变量出现（NameOccurence)是否位于＝左侧，即是否为变量赋值DEF
     */
    public boolean isOnLeftHandSide() {
    	SimpleNode declarator=null;
        if (location.jjtGetParent() instanceof ASTDeclarator) {
        	declarator = (ASTDeclarator) location.jjtGetParent();
        	if(declarator.getNextSibling()!=null){
            	return true;
            }
        } 
        //为了支持数组下标的定义使用定义，原有的变量出现访问层由Pri上升到Post，导致location发生变化
        //add by zhouhb
        //2011.3.23
        if (location instanceof ASTPostfixExpression && decl.getType().isArrayType()) {
        	Node assignment=location.jjtGetParent().jjtGetParent();
        	if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3){
        		return true;
        	}
        } 
        if(location.jjtGetParent() instanceof ASTPostfixExpression)
        {
        	declarator = (ASTPostfixExpression) location.jjtGetParent();
        	Node assignment=declarator.jjtGetParent().jjtGetParent();
        	if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3){
        		return true;
        	}
        	//add else branch by cmershen,2016.5.31 添加对*p=2类型的支持
        	else 
        	{
        		Node child = assignment;
        		assignment = assignment.jjtGetParent();
        		if(assignment instanceof ASTAssignmentExpression && assignment.jjtGetNumChildren()==3 && child == assignment.jjtGetChild(0)){
            		return true;
            	}
        	}
        }
        return false;
    }
    
    /**判断当前表达式是否为赋值表达式，如果赋值表达式的左右侧存在相同的变量(类似于自赋值i++的变种），则返回true
     * 例：int i=0，j=5;
     * 	i=j+i+3;
     * @author zys	2010.3.12
     * @return 
     */
    public boolean isAssignSameVar(SimpleNode node)
    {
    	Node assignmentNode=node.getFirstParentOfType(ASTAssignmentExpression.class);
    	if(assignmentNode!=null 
    			&& assignmentNode instanceof ASTAssignmentExpression
    			&& assignmentNode.jjtGetNumChildren()==3)
    	{
    		ASTUnaryExpression leftExpr=(ASTUnaryExpression)assignmentNode.jjtGetChild(0);
    		ASTAssignmentExpression rightExpr=(ASTAssignmentExpression)assignmentNode.jjtGetChild(2);
    		
    		//取得左侧变量名
    		ASTPrimaryExpression leftVar=(ASTPrimaryExpression)leftExpr.getFirstChildOfType(ASTPrimaryExpression.class);
    		String varName=leftVar.getImage();
    		
    		//取得右侧表达式中所有的变量名列表
    		List rightVars=rightExpr.findChildrenOfType(ASTPrimaryExpression.class);
    		for(Object o:rightVars)
    		{
    			if(o instanceof ASTPrimaryExpression)
    			{
    				ASTPrimaryExpression priExp=(ASTPrimaryExpression)o;
    				if(priExp.getImage().equals(varName))
    				{
    					return true;
    				}
    			}
    		}
    	}
    	return false;
    }
    /**
     * @author zys	2010.1.31
     * @return 判断当前变量出现（NameOccurence)是否为自增或自减（++ --)，即是否为变量赋值DEF
     */
    public boolean isSelfAssignment() {
    	if(location instanceof ASTPrimaryExpression){
	    	if(location.jjtGetParent() instanceof ASTPostfixExpression){
		    	ASTPostfixExpression postfixExp=(ASTPostfixExpression)location.jjtGetParent();
		    	//处理i++的情况
		    	if(postfixExp.getOperatorType().contains("++") || postfixExp.getOperatorType().contains("--"))
		    	{
		    		return true;
		    	}
		    	//处理++i的情况
		    	SimpleNode unaryExp=(SimpleNode)(postfixExp.jjtGetParent().jjtGetParent());
		    	if(unaryExp instanceof ASTUnaryExpression && (unaryExp.getOperatorType().contains("++") || unaryExp.getOperatorType().contains("--")))
		    	{
		    		return true;
		    	}
	    	}
    	}
    	return false;
    }

	public List<NameOccurrence> getEffected() {
		return effected;
	}

	public void setEffected(List<NameOccurrence> effected) {
		this.effected = effected;
	}
}
