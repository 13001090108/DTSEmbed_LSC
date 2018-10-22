package softtest.interpro.c;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.io.*;

import softtest.domain.c.interval.Domain;
import softtest.scvp.c.Position;
import softtest.scvp.c.SCVP;
import softtest.scvp.c.SCVPString;
import softtest.summary.c.MethodSummary;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.Type.*;

/**
 * 表示C语言中的函数类型
 * 
 * @author 祁鹏
 *
 */
public class Method implements Serializable {
	/** zys:包含该函数的文件名，防止不同文件的重名函数分析时冲突*/
	private String fileName;
	
	/**
	 * 函数名
	 */
	private String name;
	
	/**
	 * 函数是否接受变参，即参数个数是否可变
	 */
	private boolean isVararg = false;
	
	/**
	 * 函数的参数类型列表
	 */
	private List<CType> parameters;
	
	/**
	 * 函数的返回值类型
	 */
	private CType returnType;
	
	transient private Domain returnDomain;
	
	/**
	 * 该函数节点的函数摘要信息
	 */
	transient private MethodSummary mtSummmary;
	/*
	 * @author cmershen
	 * @date 2016.5.24
	 * 表示函数的外部影响
	 */
	
	//private HashMap<NameOccurrence, List<SCVP>> externalEffects;
	private HashMap<String, List<SCVPString>> externalEffects;
	/*
	 * @author cmershen
	 * @date 2016.5.24
	 * 表示调用点信息
	 */
	//private HashMap<Position, ArrayList<SCVP>> callerInfo;
	private HashMap<Position, ArrayList<SCVPString>> callerInfo;
	/*
	 * @author cmershen
	 * @date 2016.9.20
	 * 表示返回值信息，key为返回点的位置，value为返回参数的D，目前先处理return 1,return a,return a+b等情况。
	 */
	//private ArrayList<SCVP> returnList;
	private ArrayList<SCVPString> returnList;
	/**
	 * 函数是否会分配内存空间
	 */
	private boolean isAllocate;
//	@Override
//	public void finalize() {
//		System.out.println("Final"+this.toString());
//	}
	public Method(String fileName,String name, List<CType>parameters, CType returnType, boolean isVararg) {
		this.fileName=fileName;
		this.name = name;
		this.parameters = parameters;
		this.returnType = returnType;
		this.isVararg = isVararg;
		//added by cmershen,2016.5.24
		this.externalEffects = new HashMap<String, List<SCVPString>>();
		this.callerInfo = new HashMap<Position, ArrayList<SCVPString>>();
		//added by cmershen,2016.9.20
		this.returnList = new ArrayList<SCVPString>();
	}
	
	public void addReturnValue(Domain newValue) {
		try {
			returnDomain = newValue.clone();
		} catch (CloneNotSupportedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void setReturnValue(Domain value) {
		this.returnDomain = value;
	}
	
	@Override
	public int hashCode() {
		int ret = 0;
		ret = name.hashCode() + parameters.size();
		return ret;
	}
	
	@Override
	public boolean equals(Object o) {
		if ((o == null) || !(o instanceof Method)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		Method method = (Method)o;
		if(fileName.equals("unknown") || method.getFileName().equals("unknown"))
		{
			if(name.equals(method.getName()))
			{
				return true;
			}else
			{
				return false;
			}
		}
		if (!this.fileName.equals(method.getFileName())) {
			return false;
		}
		if (!this.name.equals(method.getName())) {
			return false;
		}
		List<CType> params = method.getParameters();
		if (this.parameters.size() != params.size()) {
			return false;
		}
		for (int i = 0; i < this.parameters.size(); i++) {
			if (!parameters.get(i).equalType(params.get(i))) {
				return false;
			}
		}
		if (this.returnType == null && method.getReturnType() == null) {
			return true;
		} else if(!this.returnType.equalType(method.getReturnType())) {
			return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		File f=new File(fileName);
		//去掉最后的.c
		String temp=f.getName();
		if(temp.matches(InterContext.SRCFILE_POSTFIX) || temp.matches(InterContext.INCFILE_POSTFIX))
			temp=temp.substring(0, temp.length()-2);
		return temp+"_"+name + "_" + parameters.size();
	}

	// getters and setters
	public MethodSummary getMtSummmary() {
		return mtSummmary;
	}

	public void setMtSummmary(MethodSummary mtSummmary) {
		this.mtSummmary = mtSummmary;
	}
	
	public Domain getReturnDomain() {
		return returnDomain;
	}
	
	public boolean isVararg() {
		return isVararg;
	}
	
	public boolean isAllocate(){
		return isAllocate;
	}
	
	public void setIsAllocate(boolean isAllocate){
		this.isAllocate = isAllocate;
	}

	public String getName() {
		return name;
	}

	public List<CType> getParameters() {
		return parameters;
	}

	public CType getReturnType() {
		return returnType;
	}

	private boolean isexit = false;
	
	public boolean isExit() {
		return isexit;
	}
	
	public void setExit(boolean isexit) {
		this.isexit = isexit;
	}
	
	
	private boolean isexcept = false;
	
	public boolean isExcept() {
		return isexcept;
	}
	
	public void setExcept(boolean isexcept) {
		this.isexcept = isexcept;
	}

	public String getFileName() {
		return fileName;
	}

	public void setFileName(String fileName) {
		this.fileName = fileName;
	}

	public HashMap<String, List<SCVPString>> getExternalEffects() {
		return externalEffects;
	}

	public void setExternalEffects(HashMap<String, List<SCVPString>> externalEffects) {
		this.externalEffects = externalEffects;
	}

	public HashMap<Position, ArrayList<SCVPString>> getCallerInfo() {
		return callerInfo;
	}

	public void setCallerInfo(HashMap<Position, ArrayList<SCVPString>> callerInfo) {
		this.callerInfo = callerInfo;
	}

	public ArrayList<SCVPString> getReturnList() {
		return returnList;
	}

	public void setReturnList(ArrayList<SCVPString> returnList) {
		this.returnList = returnList;
	}
}
