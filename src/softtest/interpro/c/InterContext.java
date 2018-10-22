package softtest.interpro.c;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import softtest.ast.c.*;
import softtest.cfg.c.VexNode;
import softtest.summary.c.MethodFeatureVisitor;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.*;

public class InterContext {
	
	/**
	 * <p>
	 * The postfix of the file for filting to process in DTSC,
	 * .cpp, .c, .CPP, .c++, .C, .cxx, .CXX, .cc, .CC
	 * </p>
	 */
	//public static String SRCFILE_POSTFIX = ".+\\.(c|C|CPP|cpp|c\\+\\+|cxx|CXX|cc|CC)$";
	public static String SRCFILE_POSTFIX = ".+\\.(c|C|c\\+\\+|cxx|CXX|cc|CC)$";

	public static String INCFILE_POSTFIX = ".+\\.(h|H|hpp|hxx)$";
	public static String IFILE_POSTFIX = ".+\\.(i|I)$";
	
	private static InterContext instance = null;
	
	private Map<String, MethodNameDeclaration> libMethods;

	/**
	 * 当前全局分析中注册的函数副作用分析访问者
	 */
	private static Set<MethodFeatureVisitor> seVisitors = new HashSet<MethodFeatureVisitor>();
	private static Set<MethodFeatureVisitor> preCondVistiors = new HashSet<MethodFeatureVisitor>();
	private static Set<MethodFeatureVisitor> postCondVisitors = new HashSet<MethodFeatureVisitor>();
	
	private InterContext() {
		libMethods = new HashMap<String, MethodNameDeclaration>();
	}
	
	public static InterContext getInstance() {
		if (instance == null) {
			instance = new InterContext();
		}
		return instance;
	}
	
	public void addLibMethodDecl(Set<MethodNameDeclaration> methodDecls) {
		for (MethodNameDeclaration methodDecl : methodDecls) {
			if (libMethods.containsKey(methodDecl.getImage())) {
				MethodNameDeclaration oldDecl = libMethods.get(methodDecl.getImage());
				
				MethodSummary mtSummary = oldDecl.getMethodSummary();
				if (mtSummary != null) {
					mtSummary.addSummary(methodDecl.getMethodSummary());
				} else {
					oldDecl.setMethod(methodDecl.getMethod());
				}
			} else {
				libMethods.put(methodDecl.getImage(), methodDecl);
			}
		}
	}
	
	public Map<String, MethodNameDeclaration> getLibMethodDecls() {
		return libMethods;
	}
	
	public void clean() {
		libMethods.clear();
		seVisitors.clear();
		preCondVistiors.clear();
		postCondVisitors.clear();
	}
	
	public static void clear() {
		if (instance != null) {
			instance.clean();
		}
		instance = null;
	}
	
	public static void addSideEffectVisitor(MethodFeatureVisitor seVisitor) {
		seVisitors.add(seVisitor);
	}
	
	public static void addPreConditionVisitor(MethodFeatureVisitor preVisitor) {
		preCondVistiors.add(preVisitor);
	}
	
	public static void addPostConditionVisitor(MethodFeatureVisitor postVisitor) {
		postCondVisitors.add(postVisitor);
	}
	
	public static MethodSummary getMethodSummary(VexNode node) {
		SimpleNode simpleNode = node.getTreenode();
		MethodNameDeclaration methodDecl = null;
		if (simpleNode instanceof ASTFunctionDefinition) {
			methodDecl = ((ASTFunctionDefinition)simpleNode).getDecl();
		} 
		if (methodDecl != null) {
			Method method = methodDecl.getMethod();
			if (method == null) {
				return null;
			}
			MethodSummary summary = method.getMtSummmary();
			if (summary == null) {
				summary = new MethodSummary();
				method.setMtSummmary(summary);
			}
			return summary;
		}
		return null;
	}
	
	/**zys:2010.8.9	这个函数多余，没必要使用它！！！！ */
	public static MethodNameDeclaration getMethodDecl(VexNode node) {
		SimpleNode simpleNode = node.getTreenode();
		MethodNameDeclaration methodDecl = null;
		if (simpleNode instanceof ASTFunctionDefinition) {
			methodDecl = ((ASTFunctionDefinition)simpleNode).getDecl();
		} 
		return methodDecl;
	}
	
	public static void cntMethodFeture(VexNode vexNode) {
		for (MethodFeatureVisitor seVisitor : seVisitors) {
			seVisitor.visit(vexNode);
		}
		for (MethodFeatureVisitor preCondVisitor : preCondVistiors) {
			preCondVisitor.visit(vexNode);
		}
		for (MethodFeatureVisitor postCondVisitor : postCondVisitors) {
			postCondVisitor.visit(vexNode);
		}
	}
}
