package softtest.fsmanalysis.c;

public class Report {

	private String eclass;
	
	private String fsmName = "";
	
	private String fileName = "";
	
	private String relatedVarName = "";
	
	private int beginLine = 0;
	
	private int errorLine = 0;
	private int errorColumn = 0;
	
	private String desp = "";
	
	private String srcCode = "";
	
	private String preCond = "";
	
	private String traceInfo = "";
	
	private String IPMethod = "";
	
	private String dscvp = "";
	
	public String getDSCVP() {
		return dscvp;
	}
	public void setDSCVP(String dscvp) {
		this.dscvp = dscvp;
	}
	
	public String getIPMethod(){
		return IPMethod;
	}
	public void setIPMethod(String IPMethod){
		this.IPMethod = IPMethod; 
	}
	
	public String getDesp() {
		return desp;
	}

	public void setDesp(String desp) {
		this.desp = desp;
	}

	public String getEclass() {
		return eclass;
	}

	public void setEclass(String eclass) {
		this.eclass = eclass;
	}

	public String getPreCond() {
		return preCond;
	}

	public void setPreCond(String preCond) {
		this.preCond = preCond;
	}

	public String getSrcCode() {
		return srcCode;
	}

	public void setSrcCode(String srcCode) {
		this.srcCode = srcCode;
	}

	public String getTraceInfo() {
		return traceInfo;
	}

	public void setTraceInfo(String traceInfo) {
		this.traceInfo = traceInfo;
	}

	public Report(String fsmName, String fileName, String relatedVarName, int beginLine, int errorLine) {
		this.fsmName = fsmName;
		this.fileName = fileName;
		this.relatedVarName = relatedVarName;
		this.beginLine = beginLine;
		this.errorLine = errorLine;
	}

	public int getBeginLine() {
		return beginLine;
	}

	public void setBeginLine(int beginLine) {
		this.beginLine = beginLine;
	}

	public int getErrorLine() {
		return errorLine;
	}

	public void setErrorLine(int errorLine) {
		this.errorLine = errorLine;
	}

	public int getErrorColumn() {
		return errorColumn;
	}

	public void setErrorColumn(int errorColumn) {
		this.errorColumn = errorColumn;
	}
	
	public String getFileName() {
		return fileName;
	}

	public String getFsmName() {
		return fsmName;
	}

	public void setFsmName(String fsmName) {
		this.fsmName = fsmName;
	}

	public String getRelatedVarName() {
		return relatedVarName;
	}

	public void setRelatedVarName(String relatedVarName) {
		this.relatedVarName = relatedVarName;
	}
	
	public boolean equals(Object other) {
		if (!(other instanceof Report)) {
			return false;
		}
		Report report = (Report)other;
		if (!fsmName.equals(report.getFsmName())) {
			return false;
		}
		if (!eclass.equals(report.getEclass())) {
			return false;
		}
		if (!fileName.equals(report.getFileName())) {
			return false;
		}
		if (!relatedVarName.equals(report.getRelatedVarName())) {
			return false;
		}
		if (beginLine != report.getBeginLine()) {
			return false;
		} else if (fsmName.equals("NPD")) {
			// NPD类型错误，同一变量申明只报一个IP
			return true;
		}
		if (errorLine != report.getErrorLine()) {
			return false;
		}
		if (errorColumn != report.getErrorColumn()) {
			return false;
		}
		if (!desp.equals(report.getDesp())) {
			return false;
		}
		if (!srcCode.equals(report.getSrcCode())) {
			return false;
		}
		if (!preCond.equals(report.getPreCond())) {
			return false;
		}
		if (!traceInfo.equals(report.getTraceInfo())) {
			return false;
		}
		return true;
	}
	
	public int hashCode() {
		return fileName.hashCode() + relatedVarName.hashCode() + beginLine;
	}
}
