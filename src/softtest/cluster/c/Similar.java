/**
 * 
 */
package softtest.cluster.c;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import softtest.dscvp.c.DSCVPElement;
import softtest.scvp.c.SCVP;
import softtest.symboltable.c.NameOccurrence;
import edu.emory.mathcs.backport.java.util.Arrays;
import edu.emory.mathcs.backport.java.util.Collections;

/**
 * @author：JJL
 * @date: 2016年10月10日
 * @description:
 */
public class Similar {
	int sameLength = 0;
	//警报间的相似度
	public Similar() {

	}
	//计算两个警报的相似关系
	public void computeRelated (SimpleBean defect1, SimpleBean defect2, List<SimpleBean> dblist) {
		//相同变量，定位关联-JJL,2016-11-14
/**		boolean sameVariable = false;
		if (isSameVariable(defect1, defect2)) {
			sameVariable = true;
		}*/
		
		//如果警报从属等价类， 且此等价类已经进行相似关联，则跳出处理
		if (isNotNull(defect1.getEqual())) {
			if (defect2.getRelated() != null && defect2.getRelated().contains("E(" + defect1.getEqual() + ")")) {
				return;
			}
		}
		if (isNotNull(defect2.getEqual())) {
			if (defect1.getRelated() != null && defect1.getRelated().contains("E(" + defect2.getEqual() + ")")) {
				return;
			}
		}
		
		
		//第一层不是变量的定值，get child
		HashSet<DSCVPElement> fSet1 = getDSCVP(defect1.getF());
		HashSet<DSCVPElement> fSet2 = getDSCVP(defect2.getF());
		//solove NullPointerException, JJL,2016-11-1
		int len = 0;
		boolean[] condition = new boolean[1];
		condition[0] = false;
		if (fSet1 != null && fSet2 != null) {
			for (DSCVPElement x: fSet1) {
				for (DSCVPElement y: fSet2) {
					sameLength = 0;
					getSimilarLayer(x, y, 0, condition);
					if (len < sameLength) {
						len = sameLength;
					}							
				}
			}
		}
		
		if (len > 0) {
			addRelate(defect1, defect2, len, dblist, condition);
			//相似关系中是否可以生成蕴含故障，add by JJL,20161227
			getInclusion(defect1, defect2);
		}

	}
/**	
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
		if (isEqual(file1, file2) && isEqual(method1, method2) && isEqual(variable1, variable2) && isEqual(startLine1, startLine2)) {
			return true;
		}
		return false;
	}
*/
	//得到警报定值信息中子节点的集合
	public HashSet<DSCVPElement> getDSCVP (DSCVPElement d) {
		if (d == null) {
			return null;
		}
		HashMap<String, HashSet<DSCVPElement>> child = d.getChild();
		for (Entry<String, HashSet<DSCVPElement>> entry : child.entrySet()) {
			String key = entry.getKey();
			HashSet<DSCVPElement> value = child.get(key);
			return value;
//			Iterator i = value.iterator();//先迭代出来  
//	        while(i.hasNext()){//遍历  
//	        	return (DSCVPElement) i.next();  
//	        }  
	        //value指向一个hashset，第一层有可能是多个DSCVP的集合
		}
		return null;
	}
	//计算相似度
	public void getSimilarLayer(DSCVPElement F1, DSCVPElement F2, int len, boolean[] condition) {
		if (len > sameLength) {
			sameLength = len;
		}
		if (F1 != null && F2 != null) {
			//结构相同时往下寻找有无相同子节点
			if (isSameStructure(F1, F2)) {		
				sameLength = Math.max(sameLength, len+1);//jjl,10-31
				HashMap<String, HashSet<DSCVPElement>> Fchild1;
				HashMap<String, HashSet<DSCVPElement>> Fchild2;
				Fchild1 = F1.getChild();
				Fchild2 = F2.getChild();
				HashSet<DSCVPElement> DSCVP1 = new HashSet<DSCVPElement>();
				HashSet<DSCVPElement> DSCVP2 = new HashSet<DSCVPElement>();
				for (Map.Entry<String, HashSet<DSCVPElement>> entry : Fchild1.entrySet()) {
					DSCVP1.addAll(entry.getValue());
				}  
				for (Map.Entry<String, HashSet<DSCVPElement>> entry : Fchild2.entrySet()) {
					DSCVP2.addAll(entry.getValue());
				}
				for (DSCVPElement x: DSCVP1) {
					for (DSCVPElement y: DSCVP2) {
						if (isSameStructure(x, y)) {
							getSimilarLayer(x, y, len+1, condition);
						}
					}
				}			
			} else if (isSameWithoutCondition(F1, F2)) {//add by JJL, 2017/1/10
				condition[0] = true;
				
				sameLength = Math.max(sameLength, len+1);//jjl,10-31
				HashMap<String, HashSet<DSCVPElement>> Fchild1;
				HashMap<String, HashSet<DSCVPElement>> Fchild2;
				Fchild1 = F1.getChild();
				Fchild2 = F2.getChild();
				HashSet<DSCVPElement> DSCVP1 = new HashSet<DSCVPElement>();
				HashSet<DSCVPElement> DSCVP2 = new HashSet<DSCVPElement>();
				for (Map.Entry<String, HashSet<DSCVPElement>> entry : Fchild1.entrySet()) {
					DSCVP1.addAll(entry.getValue());
				}  
				for (Map.Entry<String, HashSet<DSCVPElement>> entry : Fchild2.entrySet()) {
					DSCVP2.addAll(entry.getValue());
				}
				for (DSCVPElement x: DSCVP1) {
					for (DSCVPElement y: DSCVP2) {
						if (isSameStructure(x, y)) {
							getSimilarLayer(x, y, len+1, condition);
						}
					}
				}
				
			}//end isSameWithoutCondition(F1, F2)
			
		}
	}
	//判断两个定值信息是否拥有相同的结构
	public boolean isSameStructure(DSCVPElement F1, DSCVPElement F2) {
		if (F1.getS() == null && F2.getS() == null) {
			return /*isSameVariable() ||*/ haveSameC(F1, F2) || haveSameV(F1, F2);
		} else {
			return isEqual(F1.getS(), F2.getS());
		}
		
	}
	//判断两个定值信息在不考虑条件的情况下是否拥有相同的结构
	public boolean isSameWithoutCondition (DSCVPElement F1, DSCVPElement F2) {
		String s1 = F1.getS();
		String s2 = F2.getS() ;
		if (s1 != null && s2 != null) {
			if (s1.contains("#")) {
				s1 = s1.substring(0, s1.indexOf("#"));
			} else if (s1.contains("$")) {
				s1 = s1.substring(0, s1.indexOf("$"));
			} 
			if (s2.contains("#")) {
				s2 = s2.substring(0, s2.indexOf("#"));
			} else if (s2.contains("$")) {
				s2 = s2.substring(0, s2.indexOf("$"));
			}
			return isEqual(s1, s2);
		}
		return false;
	}
	//判断两个定值信息是否拥有相同的常量
	public boolean haveSameC(DSCVPElement F1, DSCVPElement F2) {
		List<String> constants1 = F1.getSCVP().getOccs();
		List<String> constants2 = F2.getSCVP().getOccs();
		if (constants1.size() !=  constants2.size())
			return false;
		Collections.sort(constants1);
		Collections.sort(constants2);
		for (int i=0; i<constants1.size(); i++) {
			if (!constants1.get(i).equals(constants2.get(i)))
				return false;
		}
		return true;
	}
	//判断两个定值信息是否拥有相同的变量
	public boolean haveSameV(DSCVPElement F1, DSCVPElement F2) {
		List<String> occs1 = F1.getSCVP().getOccs();
		List<String> occs2 = F2.getSCVP().getOccs();
		Collections.sort(occs1);
		Collections.sort(occs2);
		for (int i=0; i<occs1.size(); i++) {
			for (int j=0; j<occs2.size(); j++) 
				if (occs1.get(i).equals(occs2.get(i)))
					return true;
		}
		return false;
	}
	//得到最少确认数量
	void getCtrlInSimilar (int[][] similarNum) {
		int dbLen = similarNum.length;
		for (int i=0; i<dbLen; i++) {
			for (int j=i+1; j<dbLen; j++) {
				if (similarNum[i][1] < similarNum[j][1]) {
					int temp0 = similarNum[i][0];
					int temp1 = similarNum[i][1];
					similarNum[i][0] = similarNum[j][0];
					similarNum[i][1] = similarNum[j][1];
					similarNum[j][0] = temp0;
					similarNum[j][1] = temp1;
				}
			}
		}
	}
	
	public void visitSimilarRelationship (String similarStr, List<SimpleBean> dblist) {
		if (similarStr != null && !similarStr.equals("")) {
			String[] arr = similarStr.split(";");
			for (int i=0; i<arr.length; i++) {
				String s = arr[i].substring(0, arr[i].indexOf("."));
				if (s.contains("E")) {
					visitEqualRelationship(s.substring(2, s.length()-1), dblist);
				} else {
					int num = Integer.valueOf(s);
					dblist.get(num-1).visitSimilar(true);
				}
				
			}
		}
	}
	
	public void visitEqualRelationship(String equal, List<SimpleBean> dblist) {
		for (int i=0; i<dblist.size(); i++) {
			SimpleBean sb = dblist.get(i);
			if (isNotNull(sb.getEqual()) && sb.getEqual().equals(equal)) {
//				if (sb.getVisited() == true)
//					break;
				sb.visitSimilar(true);
			}
		}
	}
	//计算需要确认的相似警报数量，以及包含的警报数量
	public HashMap<Integer, Integer> relatedRate (int[][]similarNum, List<SimpleBean> dblist) {
		int ctrlNum = 0;
		int sNum = 0;
		
		getCtrlInSimilar (similarNum);
		for (int i=0; i<similarNum.length; i++) {
			if (similarNum[i][1] == 0) {
				break;
			}
			sNum += 1;
			SimpleBean sb = dblist.get(similarNum[i][0]);
			if (sb.getVisited() == false) {
				sb.visitSimilar(true);
				ctrlNum += 1;
				
				//如果故障存在等价关系，可一起确认
				if (isNotNull(sb.getEqual())) {
					visitEqualRelationship(sb.getEqual(), dblist);
				}
				//确认存在相似关系的故障
				visitSimilarRelationship(sb.getRelated(), dblist);
			}
		}
		HashMap<Integer, Integer> similar = new HashMap<Integer, Integer>();
		similar.put(ctrlNum, sNum);
		return similar;
	}
/**	
	public int relatedRate(List<SimpleBean> dblist) {
		// String[] relatedStr = new String[]{};
		HashMap<String, String> map = new HashMap<String, String>();
		int relatedNum = 0;
		int relatedClass = 0;
		int j = 1;
		for (int i = 0; i < dblist.size(); i++) {
			SimpleBean defect = dblist.get(i);
			String r = defect.getRelated();
			if (isNotNull(r)) {
				// relatedStr[i] = defect.getRelated();
				relatedNum++;
				if (map.get(r) == null) {
					j = 1;
					map.put(r, String.valueOf(j));
				} else {
					String strj = (String) map.get(r);
					j = Integer.valueOf(strj);
					j++;
					map.put(r, String.valueOf(j));
				}
			}
		}
		Set sett = map.keySet();
		for (Iterator iter = sett.iterator(); iter.hasNext();) {
			String key = (String) iter.next(); // 多态
			String val = (String) map.get(key);
			relatedClass++;
			// System.out.println(key + "出现次数:" + val);
		}

		System.out.println("共" + dblist.size() + "条记录," + " 其中" + relatedClass
				+ "种相似类," + " 包含" + relatedNum + "条记录");
		return relatedNum;
	}
*/
	boolean isNotNull(String str) {
		if (str == null) {
			return false;
		} else if (str.equals("")) {
			return false;
		}
		return true;
	}

	boolean isEqual(String str1, String str2) {
		if (str1 == null && str2 == null) {
			return true;
		} else if (str1 != null && str2 != null) {
			if (str1.equals(str2)) {
				return true;
			}
		}
		return false;
	}
	//将相似关系写入警报
	void addRelate(SimpleBean sb1, SimpleBean sb2, int layer, List<SimpleBean> dblist, boolean[] condition) {
		String s1 = sb1.getRelated();
		String s2 = sb2.getRelated();
		StringBuilder r1 = new StringBuilder();
		StringBuilder r2 = new StringBuilder();
		if (s1 != null) {
			r1 = new StringBuilder(s1);
		}
		if (s2 != null) {
			r2 = new StringBuilder(s2);
		}
		//S不包含条件“#”，“$”时相等, condition,3.C1,  add by JJL, 2017/1/9
		String similarLayer = String.valueOf(layer);
		if (condition[0]) {
			similarLayer = "C" + similarLayer;
		}
		
		//当某一警报属于某等价类时，直接加入等价类名E(2).layer;
		String r1add;
		if (isNotNull(sb2.getEqual())) {
			r1add = "E(" + sb2.getEqual() + ")." + similarLayer + ";";
		} else {
			r1add = sb2.getNum() + "." + similarLayer + ";";
		}
		
		String r2add;
		if (isNotNull(sb1.getEqual())) {
			r2add = "E(" + sb1.getEqual() + ")." + similarLayer + ";";
		} else {
			r2add = sb1.getNum() + "." + similarLayer + ";";
		}

		r1.append(r1add);
		r2.append(r2add);
		sb1.setRelated(r1.toString());
		sb2.setRelated(r2.toString());
	}
/**
	String[] mergeArray(String[] arr1, String[] arr2) {// 返回要改变的记录编号
		Set set = new HashSet<String>();
		for (int i = 0; i < arr1.length; i++) {
			set.add(arr1[i]);
		}
		for (int i = 0; i < arr2.length; i++) {
			set.add(arr2[i]);
		}
		// 得到的是不重复的值，Set的长度
		// System.out.println(set.size());
		Iterator i = set.iterator();
		String[] arrays = new String[set.size()];
		int num = 0;
		while (i.hasNext()) {
			String a = (String) i.next();
			arrays[num] = a;
			num = num + 1;
			// System.out.println(num);
		}
		int[] arrayInt = new int[arrays.length];
		// 转化为int数组
		for (int s = 0; s < arrays.length; s++) {
			String str = arrays[s];
			arrays[s] = str.substring(0, str.indexOf("."));
			arrayInt[s] = Integer.parseInt(arrays[s]);
			// System.out.println(arrays[s]);
		}
		// 对结果进行排序
		Arrays.sort(arrayInt);
		for (int s = 0; s < arrayInt.length; s++) {
			arrays[s] = String.valueOf(arrayInt[s]);
		}

		return arrays;
	}

	String[] getSetNum(String str1, String str2) {
		String[] arr1 = new String[] {};
		String[] arr2 = new String[] {};
		String[] arr = new String[] {};
		if (str1 != null) {
			arr1 = str1.split(";");
		}
		if (str2 != null) {
			arr2 = str2.split(";");
		}
		arr = mergeArray(arr1, arr2);
		return arr;
	}
*/		
	int getSimilarNumber(SimpleBean sb) {
		if (isNotNull(sb.getRelated())) {
			String[] str = sb.getRelated().split(";");
			return str.length;
		}else {
			return 0;
		}
	}
	//计算警报间是否存在蕴含相似
	void getInclusion (SimpleBean sb1, SimpleBean sb2) {
		HashSet<DSCVPElement> fSet1 = getDSCVP(sb1.getF());
		HashSet<DSCVPElement> fSet2 = getDSCVP(sb2.getF());
		//sb1：D(x), sb2:D(x) U D(y)
		boolean flag1 = true;
		if (fSet1 != null && fSet2 != null) {
			for (DSCVPElement x: fSet1) {
				if (!setContains(fSet2, x)) 
					flag1 = false;
			}
		}	
		//sb2:D(x) U D(y), sb1：D(x)U D(y)U D(z)
		boolean flag2 = true;
		if (fSet1 != null && fSet2 != null) {
			for (DSCVPElement x: fSet2) {
				if (!setContains(fSet1, x)) 
					flag2 = false;
			}
		}
		
		if (flag1) { 
			sb1.setSimilarInclusion(true);
			sb1.setSimilarInclusionAlarm(sb2.getNum());
		} else if (flag2) {
			sb2.setSimilarInclusion(true);
			sb2.setSimilarInclusionAlarm(sb1.getNum());
		}
		
	}
	
	boolean setContains (HashSet<DSCVPElement> set, DSCVPElement D) {
		if (set == null || D == null)
			return false;
		for (DSCVPElement e: set) {
			if (e.getSCVP().getPosition() == D.getSCVP().getPosition())
				return true;
		}
		return false;
	}
	
}
