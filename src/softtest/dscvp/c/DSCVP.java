package softtest.dscvp.c;

/*
 * 专利中的DSCVP结构，由层次遍历DSCVPElement组成，相同层次的组合成一个DSCVP结构
 */
public class DSCVP {
	//当前层次
	int layer;
	//IP点的信息，应该包含文件，位置，类型等
	String IPinfo;
	//组合后的dscvp字符串
	StringBuilder dscvp;
	//指向下一层的dscvp结构
	DSCVP nextLayer;
	//构造函数
	public DSCVP (){
		dscvp = new StringBuilder();
	}
	//生成DSCVP，主要动作
	public void appendDSCVPString(String str){
		dscvp.append(str);
	}
	
	public StringBuilder getDscvp() {
		return dscvp;
	}
	
	public DSCVP getNextLayer() {
		return nextLayer;
	}
	
}
