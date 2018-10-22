package softtest.summary.gcc.fault;

import softtest.interpro.c.Method;
import softtest.summary.c.MethodFeature;
import softtest.symboltable.c.MethodNameDeclaration;

public class MethodRMFeature extends MethodFeature {

	public final static String METHOD_RM_FEATURE = "METHOD_MLF_FEATURE";
	
//	private MethodNameDeclaration releaseMethod;
	
	private Method relMethod;
	
	public MethodRMFeature() {
		super(METHOD_RM_FEATURE);
	}

	public void setReleaseMethod(MethodNameDeclaration releaseMethod) {
//		this.releaseMethod = releaseMethod;
		this.relMethod=new Method(releaseMethod.getFileName(),releaseMethod.getImage(),releaseMethod.getParams(),releaseMethod.getType(),false);
	}
	
//	public MethodNameDeclaration getReleaseMethod() {
//		return this.releaseMethod;
//	}
	
	public Method getReleaseMethod() {
		return this.relMethod;
	}
	
}
