package softtest.fsmanalysis.c;

public class ProjectStat {

	private String name;
	private String resultdb;
	private int fileNum;
	private int lineCnt;
	private String version;
	private int time;
	private int ipNum;
	private long syntaxTreeTime;
	private long symbolTableTime;
	private long globalAnalysisTime;
	private int timeOutfiles;
	
	public ProjectStat(String name, String resultdb, int fileNum, int lineCnt, int time, int ipNum,long syntaxTreeTime,long symbolTableTime,long globalAnalysisTime,int timeOutfiles) {
		this.name = name;
		this.fileNum = fileNum;
		this.lineCnt = lineCnt;
		this.time = time;
		this.resultdb = resultdb;
		this.ipNum = ipNum;
		this.syntaxTreeTime = syntaxTreeTime;
		this.symbolTableTime = symbolTableTime;
		this.globalAnalysisTime = globalAnalysisTime;
		this.timeOutfiles = timeOutfiles;
	}
	
	public int getFileNum() {
		return fileNum;
	}
	public void setFileNum(int fileNum) {
		this.fileNum = fileNum;
	}
	public int getLineCnt() {
		return lineCnt;
	}
	public void setLineCnt(int lineCnt) {
		this.lineCnt = lineCnt;
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public int getTime() {
		return time;
	}
	public void setTime(int time) {
		this.time = time;
	}
	public String getVersion() {
		return version;
	}
	public void setVersion(String version) {
		this.version = version;
	}

	public String getResultdb() {
		return resultdb;
	}

	public void setResultdb(String resultdb) {
		this.resultdb = resultdb;
	}

	public int getIpNum() {
		return ipNum;
	}

	public void setIpNum(int ipNum) {
		this.ipNum = ipNum;
	}
	
	public void setSyntaxTreeTime(long syntaxTreeTime){
		this.syntaxTreeTime = syntaxTreeTime;
	}
	
	public long  getSyntaxTreeTime(){
		return this.syntaxTreeTime;
	}
	
	public void setSymbolTableTime(long symbolTableTime){
		this.symbolTableTime = symbolTableTime;
	}
	
	public long  getSymbolTableTime(){
		return this.symbolTableTime;
	}
	
	public void setGlobalAnalysisTime(long globalAnalysisTime){
		this.globalAnalysisTime = globalAnalysisTime;
	}
	
	public long getGlobalAnalysisTime(){
		return this.globalAnalysisTime;
	}
	
	public void setTimeOutfiles(int timeOutfiles){
		this.timeOutfiles = timeOutfiles;
	}
	
	public int getTimeOutfiles(){
		return this.timeOutfiles;
	}
}
