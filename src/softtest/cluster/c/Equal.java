/**
 * 
 */
package softtest.cluster.c;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author：JJL
 * @date: 2016年10月10日
 * @description:
 */
public class Equal {
	public Equal () {
		
	}
	
	public void computeEqual (SimpleBean defect1, SimpleBean defect2, Cluster c) {
		if (isSameSCVP(defect1, defect2)) {
			if (isNotNull(defect1.getEqual())) {//equal字段有值
				defect2.setEqual(defect1.getEqual());
			} else {
				c.equalNum ++;
				defect1.setEqual(String.valueOf(c.equalNum));
				defect2.setEqual(String.valueOf(c.equalNum));
			}
		}
	}
/**	
	public void computeEqual (List<SimpleBean> dblist) {
		int equalNum = 0;
		for (int i = 0; i < dblist.size(); i++) {
			SimpleBean defect1 = dblist.get(i);
			for (int j = i+1; j < dblist.size(); j++) { 
				SimpleBean defect2 = dblist.get(j) ;
				//IP点为同一个变量的，改为具有相似关系，因为不同的IPLine可能具有有不同的赋值,JJL,2016-11-14
				//if (isSameVariable(defect1, defect2) || isSameSCVP(defect1, defect2)) {
				if (isSameSCVP(defect1, defect2)) {
					if (isNotNull(defect1.getEqual())) {//equal字段有值
						defect2.setEqual(defect1.getEqual());
					} else {
						equalNum ++;
						defect1.setEqual(String.valueOf(equalNum));
						defect2.setEqual(String.valueOf(equalNum));
					}
				}
			}
		
			//写入数据库
			//System.out.println(defect1.getNum() + "-" + defect1.getEqual());
		}
		equalRate (equalNum, dblist);
	}
*/	
/*
	boolean isSameVariable (SimpleBean sb1, SimpleBean sb2) {
		String category1 = sb1.getCategory();
		String category2 = sb2.getCategory();
		String file1 = sb1.getFile();
		String file2 = sb2.getFile();
		String method1 = sb1.getMethod();
		String method2 = sb2.getMethod();
		String variable1 = sb1.getVariable();
		String variable2 = sb2.getVariable();
		String startLine1 = sb1.getStartLine();
		String startLine2 = sb2.getStartLine();
		if (isSameCategory(category1, category2) && isEqual(file1, file2) && isEqual(method1, method2) 
				&& isEqual(variable1, variable2) && isEqual(startLine1, startLine2)) {
			return true;
		}
		return false;
	}
*/
	
	boolean isSameSCVP (SimpleBean sb1, SimpleBean sb2) {
		String SCVP1 = sb1.getStringF();
		String SCVP2 = sb2.getStringF();
		if (SCVP1.equals("layer: 1 \n") || SCVP2.equals("layer: 1 \n")) {
			return false;
		}
		if ( isNotNull(SCVP1) && isNotNull(SCVP2)) {
			/** modify by JJL, 取消对字符串的处理，保留变量行& P
			SCVP1 = handleDSCVP(SCVP1);
			SCVP2 = handleDSCVP(SCVP2);*/
			if (isEqual(SCVP1, SCVP2)) {
				return true;
			}
		}
		return false;
	}
/**	
	String handleDSCVP (String s) {
		s = deleteLineNumber(s);
		s = deletePosition (s);
		return s;
	}
*/	
	/**
	String deleteLineNumber (String s) {
		while (s.contains("occs=[")) {
			int start = s.indexOf("occs=[");
			int end = start;			
			for (int i = start; i < s.length(); i++) {
				if (s.charAt(i) == ']') {
					end = i;
					break;
				}
			}
			String variable = "occs=";
			String middle = s.substring(start+5, end+1);
//			System.out.println(middle);
			while (middle.indexOf(':') >= 0) {
				int x = middle.indexOf(":");
				int y = x;
				for (int i = x; i < middle.length(); i++) {
					if (middle.charAt(i) == ',' || middle.charAt(i) == ']') {
						y = i;
						break;
					}
				}
				String l = middle.substring(0, x);
				String r = middle.substring(y, middle.length());
				middle = l + r;
				//middle = middle.substring(0, x) + middle.substring(y+1, middle.length());
			}
			s = s.substring(0, start) + variable + middle.substring(1, middle.length()-1) + s.substring(end+1, s.length());
		}
		return s;
	}
*/	
/**
	String deletePosition (String s) {
		while (s.contains("position=")) {
			int start = s.indexOf("position=");
			int end = start;
			for (int i = start; i < s.length(); i++) {
				if (s.charAt(i) == ']') {
					end = i;
					break;
				}
			}
			String left = s.substring(0, start);
			String right = s.substring(end+1, s.length());
			s = left + right;
		}
		return s;
	}
*/	
	boolean isNotNull (String str) {
		if (str == null) {
			return false;
		}
		else if (str.equals("")) {
			return false;
		}
		return true;
	}
	
	boolean isEqual (String str1, String str2) {
		if (str1 == null && str2 == null) {
			return true;
		}
		else if (str1 != null && str2 != null) {
			if (str1.equals(str2)) {
				return true;
			}
		}
		return false;
	}
	
	HashMap<Integer, Integer> equalRate(Cluster c, List<SimpleBean> dblist) {
		int defectEqualNum = 0;
		for (int i = 0; i < dblist.size(); i++) {
			if (isNotNull (dblist.get(i).getEqual())) {
				defectEqualNum ++;
			}
		}
		System.out.println("共"+dblist.size()+"条记录，其中" + c.getEqualNum()+ "种等价类，包含" + defectEqualNum + "条记录");
		//计算等价率
		HashMap<Integer, Integer> equal = new HashMap<Integer, Integer>();
		equal.put(c.getEqualNum(), defectEqualNum);
		return equal;
	}
	
}
