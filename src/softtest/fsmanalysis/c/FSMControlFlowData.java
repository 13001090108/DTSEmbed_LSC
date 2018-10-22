package softtest.fsmanalysis.c;

import java.util.List;

import softtest.database.c.*;
import softtest.fsmanalysis.c.Report;

/** 用于控制流状态迭代的数据传递 */
public class FSMControlFlowData {
	/** 是否报告错误 */
	public boolean reporterror = false;

	/**
	 * 当前分析中所有错误报告的记录单元，用于单元测试
	 */
	private List<Report> reports;
	
	/**
	 * 当前分析中所有报告的记录单元，用于单元测试
	 */
	private List<Report> all_reports;
	
	/**
	 * 当前模式分析中检测出错误的个数
	 */
	public int errorNum = 0;
	
	/**
	 * 当前扫描的文件名
	 */
	private String curFileName = "";
	
	/**
	 * 当前扫描所使用的数据库
	 */
	private DBAccess db;
	
	public FSMControlFlowData() {
	}

	public void setParseFileName(String curFileName) {
		this.curFileName = curFileName;
	}
	
	public String getCurFileName() {
		return curFileName;
	}
	
	public void setDB(DBAccess db) {
		this.db = db;
	}
	public DBAccess getDB() {
		return db;
	}
	
	public void setReports(List<Report> reports) {
		this.reports = reports;
	}
	
	public void addReport(Report report) {
		if (reports == null) {
			return;
		}
		reports.add(report);
	}
	
	public List<Report> getReports() {
		return reports;
	}
	
	public void setAllReports(List<Report> reports) {
		this.all_reports = reports;
	}
	
	public void addAllReport(Report report) {
		if (all_reports == null) {
			return;
		}
		all_reports.add(report);
	}
	
	public List<Report> getAllReports() {
		return all_reports;
	}
	
	int srcFileLine = 0;
}
