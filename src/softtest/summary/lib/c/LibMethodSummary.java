package softtest.summary.lib.c;

import java.io.FileInputStream;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import softtest.ast.c.*;
import softtest.domain.c.interval.Domain;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.InterMethodVisitor;
import softtest.interpro.c.Method;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.SourceFileScope;

/**
 * 库函数函数摘要信息
 * 
 * @author qipeng
 *
 */
public class LibMethodSummary {
	
	/**
	 * <p>库函数所在的C-C++中的库名称</p>
	 */
	private String libName;
	
	/**
	 * <p>库函数名</p>
	 */
	private String methodName;
	
	/**
	 * <p>库函数的函数签名，必须符合C++语法的函数签名，用来编译生成函数摘要</p>
	 */
	private String signature;
	
	/**
	 * <p>库函数的返回值区</p>
	 */
	private Domain retDomain;
	
	/**
	 * <p>当前库函数的所有的函数特征信息</p>
	 */
	private Set<LibMethodDesp> features;
	
	/**
	 * 库函数是否会分配内存空间
	 */
	private boolean isAllocate;
	
	public LibMethodSummary(String libName, String methodName, String signature) {
		this.libName = libName.toLowerCase();
		this.methodName = methodName;
		this.signature = signature;
		features = new HashSet<LibMethodDesp>();
		LibManager libManager = LibManager.getInstance();
		libManager.addLib(this.libName, this);
	}

	/**
	 * 添加函数特征信息
	 * 
	 */
	public void addFeature(LibMethodDesp feature) {
		features.add(feature);
	}
	
	/**
	 * 设置库函数返回值区间
	 * @param retDomain
	 */
	public void setRetDomain(Domain retDomain) {
		this.retDomain = retDomain;
	}
	
	public Domain getRetDomain() {
		return this.retDomain;
	}

	/**
	 * 设置库函数是否分配内存空间
	 * @param isAllocate
	 */
	public void setIsAllocate(boolean isAllocate){
		this.isAllocate = isAllocate;
	}
	/**
	 * 根据函数签名，编译生成函数声明，再根据函数特征信息，生成函数摘要
	 * 将该函数对应的所有XML摘要描述全部转化成函数摘要
	 * @return
	 */
	public MethodNameDeclaration compileSummary() {
		//第一步：生成抽象语法树AST
		CParser parser = CParser.getParser(new CCharStream(new StringReader(this.signature)));
		ASTTranslationUnit root=null;
		try {
			root = parser.TranslationUnit();
		} catch (ParseException e) {
			e.printStackTrace();
		}
		ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
		root.jjtAccept(sc, null);
		SourceFileScope scope = (SourceFileScope)root.getScope();
		Map<MethodNameDeclaration, ArrayList<NameOccurrence>> methods = scope.getMethodDeclarations();
		MethodNameDeclaration methodDecl = null;
		if (methods.size() != 0) {
			methodDecl = methods.keySet().iterator().next();
		} 
		if (methodDecl != null) {
			methodDecl.setLibFunction(true);
			methodDecl.setNode(null);
			if (methodDecl.getScope() instanceof SourceFileScope) {
				methodDecl.setScope(null);
			}
			Method method = InterMethodVisitor.getMethod(methodDecl);
			methodDecl.setMethod(method);
			if(retDomain!=null)
				method.setReturnValue(retDomain);
			method.setIsAllocate(isAllocate);
			MethodSummary mtSummary = new MethodSummary();
			for (LibMethodDesp feature: features) {
				feature.createFeature(libName, root, mtSummary);
			}
			method.setMtSummmary(mtSummary);
			return methodDecl;
		}
		return null;
	}
	
	public String toString() {
		String str = this.signature + "\n";
		for (LibMethodDesp feature : features) {
			str += feature.type + "[" + feature.value + "]";
		}
		str += "\n";
		if (retDomain != null) {
			str += retDomain.toString();
		}else if(isAllocate){
			str += new Boolean(isAllocate).toString();
		}
		return str;
	}
}
