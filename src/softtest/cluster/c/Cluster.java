/**
 * 
 */
package softtest.cluster.c;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import softtest.database.c.DBAccess;
import softtest.dts.c.DTSC;

/**
 * @author：JJL
 * @date: 2016年11月15日
 * @description:
 */
public class Cluster {
	int equalNum = 0;//等价类的数量
	public Cluster() {
		
	}
	
	public int getEqualNum () {
		return this.equalNum;
	}
	//对list中每两个警报进行关联关系构建
	public void startCluster(List<SimpleBean> dblist, DBAccess dbAccess) {
		Equal en = new Equal();
		Similar rn = new Similar();
		Cluster c = new Cluster();
		for (int i = 0; i < dblist.size(); i++) {
			SimpleBean defect1 = dblist.get(i);
			for (int j = i + 1; j < dblist.size(); j++) {
				SimpleBean defect2 = dblist.get(j);
				if (isSameCategory(defect1.getCategory(), defect2.getCategory()) ) {
					if (isNotNull(defect1.getStringF()) && isNotNull(defect2.getStringF())) {
						if (defect1.getCategory().contains("RL")) {
							continue;
						} 
						en.computeEqual (defect1, defect2, c);
					}
				}
			}
		}
		
		//存储每条缺陷对应的缺陷个数
		int[][] similarNum = new int[dblist.size()][2];
		
		for (int i = 0; i < dblist.size(); i++) {
			SimpleBean defect1 = dblist.get(i);
			for (int j = i + 1; j < dblist.size(); j++) {
				SimpleBean defect2 = dblist.get(j);
				if (isSameCategory(defect1.getCategory(), defect2.getCategory()) ) {
					if (isNotNull(defect1.getStringF()) && isNotNull(defect2.getStringF())) {
						//当两个IP不为等价类时进行相似关联：equal都为null || equal不相等
						if ( !isNotNull(defect1.getEqual()) || !isNotNull(defect2.getEqual()) 
								|| !isEqual(defect1.getEqual(), defect2.getEqual())) {//
							rn.computeRelated (defect1, defect2, dblist);
						}
					}
				}
			}
			
			similarNum[i][0] = i;
			similarNum[i][1] = rn.getSimilarNumber(defect1);			
		}
		
		HashMap<Integer, Integer> equal = en.equalRate(c, dblist);//在writeDB中实现
		HashMap<Integer, Integer> similar = rn.relatedRate(similarNum, dblist);
		// 写入数据库
		writeDB(dblist, dbAccess, equal, similar);
	}
	//判断两个缺陷模式是否相同
	boolean isSameCategory (String c1, String c2) {
		List <Set> list = new ArrayList <Set>();
		Set <String> s1 = new HashSet<String>();
		s1.add("BO");
		s1.add("BO_PRE");
		list.add(s1);
		Set <String> s2 = new HashSet<String>();
		s2.add("IAO");
		s2.add("IAO_PRE");
		list.add(s2);
		Set <String> s3 = new HashSet<String>();
		s3.add("MLF");
		s3.add("MLF_PRE");
		s3.add("MLF_LOOP");
		s3.add("MLF_FREE");
		s3.add("MLF_WRONG");
		list.add(s3);
		Set <String> s4 = new HashSet<String>();
		s4.add("NPD");
		s4.add("NPD_Check");
		s4.add("NPD_EXP");
		s4.add("NPD_PARAM");
		s4.add("NPD_PRE");
		s4.add("NPD_POST");
		list.add(s4);
		Set <String> s5 = new HashSet<String>();
		s5.add("OOB");
		s5.add("OOB_Check");
		s5.add("OOB_PRE");
		list.add(s5);
		Set <String> s6 = new HashSet<String>();
		s6.add("RL");
		s6.add("RL_PRE");
		list.add(s6);
		Set <String> s7 = new HashSet<String>();
		s7.add("UFM");
		s7.add("UFM_PRE");
		s7.add("UFM_EXP");
		list.add(s7);
		Set <String> s8 = new HashSet<String>();
		s8.add("UVF");
		s8.add("UVF_EXP");
		list.add(s8);
		
		if (isEqual(c1, c2)) {
			return true;
		}
		for (int i = 0; i < list.size(); i++) {
			Set s = list.get(i);
			if (s.contains(c1) && s.contains(c2)) {
				return true;
			}
		}
		return false;
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
	
	/** 当字符串不空，返回true*/
	boolean isNotNull(String str) {
		if (str == null) {
			return false;
		} else if (str.equals("")) {
			return false;
		}
		return true;
	}
	//计算提高效率并将关联结果写进数据库
	public void writeDB (List<SimpleBean> dbList, DBAccess dbAccess, HashMap<Integer, Integer> equal, HashMap<Integer, Integer> similar) { 
		int IPNum = 0;
		Set<String> inclusionMainSet = new HashSet<String>();
		Set<String> inclusionTotalSet = new HashSet<String>();
		Map<String, Set<String>> inclusionMap = new HashMap<String, Set<String>>();
		
		for (int j = 0; j < dbList.size(); j++) {
			SimpleBean listSB = dbList.get(j);			
			//计算可定位IP
			if (listSB.getF() != null && !listSB.getF().getChild().isEmpty()) {
				IPNum += 1;
			}
			//计算相似关系蕴含IP
			if (listSB.getSimilarInclusion()) {
				inclusionMainSet.add(listSB.getNum());
				Set<String> set = listSB.getSimilarInclusionAlarm();
				if(set != null) {
					for (String alarm: set) {
						inclusionTotalSet.add(alarm);
						if (inclusionMap.containsKey(listSB.getNum())) {
							inclusionMap.get(listSB.getNum()).add(alarm);
						} else {
							Set<String> addSet = new HashSet<String>();
							addSet.add(alarm);
							inclusionMap.put(listSB.getNum(), addSet);
						}
					}
				}
			}
		}
		dbAccess.writeAccessToCluster(dbList);
		dbAccess.closeDataBase();
		//System.out.println("共有" + dbList.size() + "条记录, 其中可定位IP数量：" + IPNum);
		
		int equalSet = 0, equalNum = 0;
		for (Entry<Integer, Integer> entry : equal.entrySet()) {
			equalSet = entry.getKey();
			equalNum = entry.getValue();
			break;
		}
		
		//System.out.println("等价类："+ equalSet+"中，包含" + equalNum + "条，提高确认效率："+ (double)(equalNum-equalSet)/IPNum);
		
		int similarCtrl = 0, similarNum = 0;
		for (Entry<Integer, Integer> entry: similar.entrySet()) {
			similarCtrl = entry.getKey();
			similarNum = entry.getValue();
		}
		
		//System.out.println("相似类："+ similarCtrl+ "中,可由此确认"+ similarNum + "条，提高确认效率："+ (double)(similarNum-similarCtrl)/similarNum);
		
		//System.out.println("相似类中 蕴含IP的数量为：" + inclusionMainSet.size()+ "，分别为：" + inclusionMainSet);
		
		//System.out.println("有上述蕴含IP得到的相似关系警报数量为：" + inclusionTotalSet.size()+ "，分别为：" + inclusionTotalSet);
		Set<String> inclusionSet = new HashSet<String>();
		inclusionSet.addAll(inclusionMainSet);
		inclusionSet.addAll(inclusionTotalSet);
		//System.out.println("蕴含相似共包含IP数量："+inclusionSet.size() +", 映射关系为：" + inclusionMap+", 占相似IP数量："+(double)inclusionSet.size()/similarNum);
		//System.out.println("-----------------------------------------");
		
		Logger logger =Logger.getLogger(DTSC.class);
		logger.info("共有" + dbList.size() + "条记录, 其中可定位IP数量：" + IPNum);
		logger.info("等价类："+ equalSet+"中，包含" + equalNum + "条，提高确认效率："+ (double)(equalNum-equalSet)/IPNum);
		logger.info("相似类："+ similarCtrl+ "中,可由此确认"+ similarNum + "条，提高确认效率："+ (double)(similarNum-similarCtrl)/similarNum);
		logger.info("相似类中 蕴含IP的数量为：" + inclusionMainSet.size()+ "，分别为：" + inclusionMainSet);
		logger.info("有上述蕴含IP得到的相似关系警报数量为：" + inclusionTotalSet.size()+ "，分别为：" + inclusionTotalSet);
		logger.info("蕴含相似共包含IP数量："+inclusionSet.size() +", 占相似IP数量："+(double)inclusionSet.size()/similarNum +", 映射关系为：" + inclusionMap);
	}
}
