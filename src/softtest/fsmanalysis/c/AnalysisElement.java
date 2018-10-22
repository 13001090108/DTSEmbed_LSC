package softtest.fsmanalysis.c;

/**
 * DTSC一次分析的最小单元是.C文件，而具体分析过程中是分析预处理得到的中间文件，
 * 因此这个类记录分析单元对应的信息
 * @author 
 *
 */
public class AnalysisElement implements Comparable<AnalysisElement> {

	private String fileName;
	
	private String interFileName;
	
	private boolean cppError = false;
	
	/**
	 * 该分析单元节点的出度，当前分析单元体依赖多少个外部的分析单元
	 */
	private int outDegree;
	/**
	 * 该分析单元节点的入度，当前分析单元被多少个外部的分析单元依赖
	 */
	private int inDegree;
	
	/**
	 * 深度遍历用于查找环的
	 */
	private int color;
	
	public AnalysisElement(String fileName, String interFileName) {
		this.fileName = fileName;
		this.interFileName = interFileName;
		outDegree = 0;
		inDegree = 0;
		color = 0;
	}
	
	public AnalysisElement(String fileName) {
		this(fileName, "");
		outDegree = 0;
		inDegree = 0;
		color = 0;
	}

	public String getFileName() {
		return fileName;
	}

	public void setFileName(String fileName) {
		this.fileName = fileName;
	}

	public String getInterFileName() {
		return interFileName;
	}

	public void setInterFileName(String interFileName) {
		this.interFileName = interFileName;
	}
	
	public void setCError(boolean cppError) {
		this.cppError = cppError;
	}
	
	public boolean isCError() {
		return cppError;
	}
	

	public int getOutDegree() {
		return outDegree;
	}
	
	public void setOutDegree(int degree) {
		this.outDegree = degree;
	}
	
	/**
	 * 更新函数节点的入度
	 */
	public void incOutDegree() {
		this.outDegree++;
	}
	
	public void decOutDegree() {
		this.outDegree--;
	}
	
	public int getInDegree() {
		return inDegree;
	}
	
	/**
	 * 更新函数节点的入度
	 */
	public void incInDegree() {
		this.inDegree++;
	}
	
	public void decInDegree() {
		this.inDegree--;
	}
	
	public void setColor(int color) {
		this.color = color;
	}
	
	public int getColor() {
		return color;
	}
	
	@Override
	public String toString() {
		return fileName;
	}

	public int compareTo(AnalysisElement o) {
		return fileName.compareTo(o.getFileName());
	}
	
	@Override
	public int hashCode() {
		return fileName.hashCode();
	}
	
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AnalysisElement))
			return false;
		AnalysisElement ae=(AnalysisElement)obj;
		if(fileName.equals(ae.fileName))
			return true;
		else 
			return false;
	}
}
