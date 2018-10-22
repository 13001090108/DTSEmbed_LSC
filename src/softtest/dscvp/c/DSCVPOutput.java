package softtest.dscvp.c;

import java.util.LinkedList;
import java.util.List;

/* 
 * 用于输出的DSCVP结构，包含所有IP点的
 * 生成方法：层次遍历DSCVP，将相同层次的组合，每层输出一个
 * 
 */
public class DSCVPOutput {
	//所有IP点的第一层DSCVP指针
	List<DSCVP> dscvplist = new LinkedList<DSCVP>();
	//向链表中添加元素
	public void add(DSCVP dscvp){
		dscvplist.add(dscvp);
	}
	//从链表中删除元素
	public void remove(DSCVP dscvp){
		dscvplist.remove(dscvp);
	}
	
}
