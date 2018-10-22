package softtest.rules.gcc.safety.BO;



import java.util.ArrayList;

import softtest.symboltable.c.MethodNameDeclaration;




public class BOFunction {
	public String name;
	public int bufIndex; //对于BOType.FORMATIN，记录起始参数位置
	public int srcIndex;
	public int limitLen;
	public BOType type;
	
	public BOFunction(String name, int bufIndex, int srcIndex, int limitLen, BOType type) {
		this.name = name;
		this.bufIndex = bufIndex;
		this.srcIndex = srcIndex;
		this.limitLen = limitLen;
		this.type = type;
	}
	
	public BOFunction(String name, int bufIndex, int srcIndex, BOType type) {
		this(name, bufIndex, srcIndex, -1, type);
	}
	
	public static ArrayList<BOFunction> getBoFuncs() {
		ArrayList<BOFunction> bofuncs = new ArrayList<BOFunction>();
		bofuncs.add(new BOFunction("gets", 0, -1, BOType.FORBIDDEN));
		//bofuncs.add(new BOFunction("getenv", 0, -1, BOType.FORBIDDEN));
		bofuncs.add(new BOFunction("getwd", 0, -1, BOType.FORBIDDEN));
		bofuncs.add(new BOFunction("snprintf", 0, 2, 1, BOType.FORMATSTRING));
		bofuncs.add(new BOFunction("_snprintf", 0, 2, 1, BOType.FORMATSTRING));
		//bofuncs.add(new BOFunction("vsnprintf", 0, 2, 1, BOType.FORMATSTRING));
		//bofuncs.add(new BOFunction("_vsnprintf", 0, 2, 1, BOType.FORMATSTRING));
		bofuncs.add(new BOFunction("sprintf", 0, 1, BOType.FORMATSTRING));
		//bofuncs.add(new BOFunction("swprintf", 0, 1, BOType.FORMATSTRING));
		//bofuncs.add(new BOFunction("vswprintf", 0, 1, BOType.FORMATSTRING));
		bofuncs.add(new BOFunction("vsprintf", 0, 1, BOType.FORMATSTRING));
		bofuncs.add(new BOFunction("fscanf", 2, 1, BOType.FORMATIN));
		//bofuncs.add(new BOFunction("fwscanf", 2, 1, BOType.FORMATIN));
		bofuncs.add(new BOFunction("scanf", 1, 0, BOType.FORMATIN));
		bofuncs.add(new BOFunction("vscanf", 1, 0, BOType.FORMATIN));
		//bofuncs.add(new BOFunction("wscanf", 1, 0, BOType.FORMATIN));
		bofuncs.add(new BOFunction("vfscanf", 1, 1, BOType.FORMATIN));
		bofuncs.add(new BOFunction("vsscanf", 0, 1, BOType.FORMATIN));
		return bofuncs;
	}
	public static BOFunction isBOfunc(MethodNameDeclaration  methodDecl){
		ArrayList<BOFunction>  bofuncs = BOFunction.getBoFuncs();
		for(BOFunction bofunc: bofuncs){
			if(methodDecl.getImage().equals(bofunc.name)){
				return bofunc;
			}
		}
		return null;
	}
}

