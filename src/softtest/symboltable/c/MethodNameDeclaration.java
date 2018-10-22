package softtest.symboltable.c;

import java.io.File;
import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;

import softtest.ast.c.*;
import softtest.callgraph.c.CVexNode;
import softtest.config.c.Config;
import softtest.interpro.c.InterCallGraph;
import softtest.interpro.c.Method;
import softtest.interpro.c.MethodNode;
import softtest.pretreatment.Pretreatment;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.Type.*;
import softtest.symboltable.c.MethodNameDeclaration;

public class MethodNameDeclaration extends AbstractNameDeclaration {
	
	private Method method;
	private static HashSet<String> libHeaders=new HashSet<String>();
	static{
		libHeaders.add("stdio.h");
		libHeaders.add("stdlib.h");
		libHeaders.add("string.h");
	}
	//added by xqing
    CVexNode cvex =null;
    
    //added by zys	2010.3.5
	private List<CType> paramList;
	private String scopeName = "";
	
    public void setCallGraphVex(CVexNode cvex){
    	this.cvex=cvex;
    }
    
    public CVexNode getCallGraphVex(){
    	return cvex;
    }
    
	public MethodNameDeclaration(ASTFunctionDefinition node) {
		super(node);
		node.setDecl(this);
		init();
	}

	public MethodNameDeclaration(ASTFunctionDeclaration node) {
		super(node);
		node.setDecl(this);
		init();
	}
	
	public MethodNameDeclaration(ASTNestedFunctionDefinition node) {
		super(node);
		node.setDecl(this);
		init();
	}
	
	public MethodNameDeclaration(ASTNestedFunctionDeclaration node) {
		super(node);
		node.setDecl(this);
		init();
	}
	
	
	private void init() {
		fileName = node.getFileName();
	}
	
	public boolean hasVarArg() {
		if (type == null) {
			return false;
		}
		CType_Function func = (CType_Function)type;
		return func.isVarArg();
	}
			
	public String getFullName() {
		StringBuffer sb = new StringBuffer();
		if(type instanceof CType_Function){
			CType_Function ftype=(CType_Function)type;
			if(ftype.getReturntype()==null){
				sb.append("int ");
			}else{
				sb.append(ftype.getReturntype().toString()).append(" ");
			}
			sb.append(getImage()+"(");
			List<CType> paramlist = ftype.getArgTypes();
			if (paramlist != null) {
				if (paramlist.size() > 0) {
					for (int i = 0; i < paramlist.size() - 1; i++) {
						sb.append(paramlist.get(i) + ", ");
					}
					sb.append(paramlist.get(paramlist.size() - 1));
				}
			}
			if(ftype.isVarArg()){
				if(paramlist != null&&paramlist.size()>0){
					sb.append(",...");
				}else{
					sb.append("...");
				}
			}
			sb.append(")");
		}
		return sb.toString();
	}
	@Override
	public boolean equals(Object o) {
		 if (! (o instanceof MethodNameDeclaration)) {
			 return false;
		 }
		 MethodNameDeclaration other = (MethodNameDeclaration) o;

		 if (!other.getImage().equals(this.getImage())) {
			 return false;
		 }
		 if (!other.getScopeName().equals(this.getScopeName())) {
			 return false;
		 }
		 if (!other.getType().equals(this.getType())) {
			 return false;
		 }
		 if (other.getParameterCount() != this.getParameterCount()) {
			 return false;
		 }
		 for (int i = 0; i < paramList.size(); i++) {
			 try {
			 if (!paramList.get(i).equals(other.getParams().get(i))) {
				 return false;
			 }
			 } catch (Exception e) {
				 e.printStackTrace();
			 }
		 }
		 return true;
	}
		
	public int hashCode() {
		int ret = 0;
		if (node!= null) {
			ret += node.getImage().hashCode();
		} 
		if (this.getScopeName() != null) {
			ret += this.getScopeName().hashCode();
		}
		return ret;
	}
	
	public SimpleNode getMethodNameDeclaratorNode() {
		//zys:如果当前节点是函数声明，则找到其定义节点；如果找不到返回空
		if(node instanceof ASTFunctionDeclaration )//|| node instanceof ASTNestedFunctionDeclaration)
		{
			SimpleNode temp=(SimpleNode) node.jjtGetParent();
			while(! (temp instanceof ASTTranslationUnit))
			{
				temp=(SimpleNode) temp.jjtGetParent();
			}
			List<Node> funcDefinitionList=temp.getfuncDefinitionList(temp);				
			for(Node n:funcDefinitionList)
			{
				ASTFunctionDefinition tempNode=(ASTFunctionDefinition)n;
				if(((ASTFunctionDeclaration)node).getType()!=null&&tempNode.getType()!=null&&((ASTFunctionDeclaration)node).getType().getName().equals(tempNode.getType().getName()))
				{
					return tempNode;
				}
			}
			
//			List<Node>	funcNestedDefinitionList=temp.findChildrenOfType(ASTNestedFunctionDefinition.class);
//			for(Node n:funcNestedDefinitionList)
//			{
//				ASTNestedFunctionDefinition tempNode=(ASTNestedFunctionDefinition)n;
//				if(((ASTFunctionDeclaration)node).getType().getName().equals(tempNode.getType().getName()))
//				{
//					return tempNode;
//				}
//			}
			return null;
		}
        return node;
    }
	
	public int getParameterCount() {
        return paramList.size();
    }

	public MethodSummary getMethodSummary() {
		getMethod();
		if (method == null) {
			return null;
		}
		return method.getMtSummmary();
	}
	
	public void setMethod(Method method) {
		this.method = method;
	}
	
	public Method getMethod() {
		if(!isLib() && getMethodNameDeclaratorNode()==null){
			InterCallGraph interGraph=InterCallGraph.getInstance();
			ConcurrentHashMap<Method, MethodNode> table=interGraph.getCallRelationTable();
			for(Method m : table.keySet()){
				if(m.getName().equals(image)){
					method=m;
					break;
				}
			}
		}
		return method;
	}
	
	public List<CType> getParams() {
		return paramList;
	}
	
	public String getScopeName() {
		return scopeName;
	}

	@Override
	public void setType(CType type) {
		if (!(type instanceof CType_Function)) {
			return;
		}
		CType_Function func = (CType_Function)type;
		this.type = func;
		paramList = func.getArgTypes();
	}
	
	public String getMethodInfo()
	{
		String str =  "Method " + getFullName() +" in line " + (node == null ? 0 : node.getBeginLine()) + " in file " + fileName;
		return str;
	}

	private boolean libFunction=false;
	
	public boolean isLib() {
		if(fileName!=null && fileName.length()>0){
			File f=new File(fileName);
			String path = fileName.replace("\\", "/");
			try {
				if(Pretreatment.systemInc==null){
					if(libHeaders.contains(f.getName().toLowerCase()))
						return true;
				}else{
					if(Config.GCC_TYPE==0){
						if(!Config.ANALYSIS_I)
							path = f.getCanonicalPath();
					}					
					for (String s : Pretreatment.systemInc) {
						s = s.replace("\\", "/");
						if (path.startsWith(s)) {
							return true;
						}
					}
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		return libFunction;
	}
	
	public void setLibFunction(boolean isLib)
	{
		this.libFunction=isLib;
	}
	@Override
	public String toString() {
		String str =  "Method " + getFullName() +" in line " + (node == null ? 0 : node.getBeginLine()) + " in file " + fileName;
		
		return str;
	}
}
