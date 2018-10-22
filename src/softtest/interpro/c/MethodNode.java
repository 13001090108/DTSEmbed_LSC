package softtest.interpro.c;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import softtest.fsmanalysis.c.AnalysisElement;

/**
 * MethodNode类用于保存全局的函数调用关系和函数摘要
 * @author zys	
 * 2010-3-6
 */
public class MethodNode {

	/**
	 * 定义该函数所对应的分析单元，包括该函数对应的源文件名，中间文件名
	 */
	private AnalysisElement element;
	
	/**
	 * 包含该函数节点的文件名
	 */
	private String tempFileName="MaybeLibMethod";
	
	/**
	 * 函数节点对应的C中的函数类型
	 */
	private Method method;
	
	/**
	 * 该函数节点调用的函数集合
	 */
	private LinkedHashSet<MethodNode> calls;
	
	/**
	 * 该函数节点调用的函数列表，有序可重复 
	 */
	private List<MethodNode> orderCalls;
	
	/**
	 * 该函数节点的出度，即调用了多少个其他函数
	 */
	private int degree;
	
	/**
	 * 该函数节点在拓扑序中的编号，用于构建全局函数调用图 
	 */
	private int toponum;
	// add by ALUO
	/** 编号 用于获取邻接矩阵 **/
	int matrixNumber; 
	
	//add by ALUO
	/** 节点已经访问过的顶点编号List **/
	ArrayList<Integer> allVisitedList;
	
	//add by ALUO
	public boolean visited = false;
	
	//add by ALUO
	public void setAllVisitedList(ArrayList<Integer> allVisitedList) {  
        this.allVisitedList = allVisitedList;  
    }  
	
	//add by ALUO
	public ArrayList<Integer> getAllVisitedList() {  
        return allVisitedList;  
    }  
	
	//add by ALUO
	public void setVisited(int j) {  
        allVisitedList.set(j, 1);  
    }
	public MethodNode(AnalysisElement element, Method method) {
		this.element = element;
		this.method = method;
		calls = new LinkedHashSet<MethodNode>();
		orderCalls = new LinkedList<MethodNode>();
		degree = 0;
	}
	
	/**
	 * 目前没法确定函数对应的分析单元，比如通过头文件导入的外部文件定义的函数声明，仅记录临时文件名
	 */
	public MethodNode(String tempFileName, Method method) {
		this.tempFileName = tempFileName;
		this.method = method;
		calls = new LinkedHashSet<MethodNode>();
		orderCalls = new LinkedList<MethodNode>();
		degree = 0;
	}
	
	/**
	 * 更新节点对应的文件名
	 * 可能之前分析的只是头文件名，当分析当定义改函数的时候需要更新节点对应的文件名
	 * 
	 * @param element
	 */
	public void updateElement(AnalysisElement element) {
		if (element == null) {
			this.element = element;
		}
		String fileName = element.getFileName();
		if (fileName.endsWith("\"")) {
			fileName = fileName.substring(0, fileName.length() - 1);
		}
		if (fileName.matches(InterContext.SRCFILE_POSTFIX) || fileName.matches(InterContext.INCFILE_POSTFIX)) {
			this.element = element;
		}
	}
	
	public void addCall(MethodNode mtNode) {
		calls.add(mtNode);
		orderCalls.add(mtNode);
	}
	
	@Override
	public String toString() {
		if (element != null) {
			return "MethodNode in file " + element.getFileName() + " : " + method;
		} else {
			return "MethodNode in file " + tempFileName + " : " + method + "(temp)";
		}
	}
	
	public AnalysisElement getElement() {
		return element;
	}
	
	public String getFileName() {
		if (element != null) {
			return element.getFileName();
		}
		return tempFileName;
	}

	public LinkedHashSet<MethodNode> getCalls() {
		return calls;
	}

	public Method getMethod() {
		return method;
	}

	public int getDegree() {
		return degree;
	}
	
	public void setDegree(int degree) {
		this.degree = degree;
	}
	
	/**
	 * 更新函数节点的出度
	 */
	public void addDegree() {
		this.degree++;
	}
	
	public void decDegree() {
		this.degree--;
	}

	public int getToponum() {
		return toponum;
	}

	public void setToponum(int toponum) {
		this.toponum = toponum;
	}

	public List<MethodNode> getOrderCalls() {
		return orderCalls;
	}
	
}
