package softtest.rules.gcc.fault;

import java.util.LinkedList;
import java.util.List;
import softtest.summary.gcc.fault.IAOType;

public class IAOFunction {
	private String funcName; //库函数名
	private int paramIndex; //参数位置（从第0位开始）
	private IAOType type; //参数的限制条件
	
	public IAOFunction(String funcName, int paramIndex, IAOType type) {
		this.funcName = funcName;
		this.paramIndex = paramIndex;
		this.type = type;
	}
	
	public static List<IAOFunction> iaoFuncList = new LinkedList<IAOFunction>();
	
	public static void setAllFunction(){
		iaoFuncList.add( new IAOFunction("acos", 0, IAOType.TRI_LIMIT) );
		iaoFuncList.add( new IAOFunction("asin", 0, IAOType.TRI_LIMIT) );
		iaoFuncList.add( new IAOFunction("atan2", 1, IAOType.NO_ZERO) );
		iaoFuncList.add( new IAOFunction("div", 1, IAOType.NO_ZERO) );
		iaoFuncList.add( new IAOFunction("ldiv", 1, IAOType.NO_ZERO) );
		iaoFuncList.add( new IAOFunction("fmod", 1, IAOType.NO_ZERO) );
		iaoFuncList.add( new IAOFunction("log", 0, IAOType.ABOVE_ZERO) );
		iaoFuncList.add( new IAOFunction("log10", 0, IAOType.ABOVE_ZERO) );
		iaoFuncList.add( new IAOFunction("sqrt", 0, IAOType.NO_BELOW_ZERO) );
	}
	
	public static List<IAOFunction> getIAOList() {
		if(iaoFuncList.size() == 0)
			setAllFunction();
		return iaoFuncList;
	}
	public String getFuncName() {
		return funcName;
	}
	public void setFuncName(String funcName) {
		this.funcName = funcName;
	}
	public IAOType getType() {
		return type;
	}
	public void setType(IAOType type) {
		this.type = type;
	}

	public int getParamIndex() {
		return paramIndex;
	}

	public void setParamIndex(int paramIndex) {
		this.paramIndex = paramIndex;
	}
	
	
}
