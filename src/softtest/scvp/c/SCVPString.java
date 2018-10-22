package softtest.scvp.c;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class SCVPString implements Serializable{
	/**
	 * @author cmershen
	 * @date 2016.10.31
	 * @description 应大海要求，将SCVP改写成String串的形式，以防止jvm堆区溢出。
	 */
	private List<String> ipOccs;
	private String structure;
	private List<String> constants;
	private List<String> occs;
	private Position position;//P域好像没耦合什么语法树。
	private String var;
	
	public String getVar() {
		return var;
	}

	public void setVar(String var) {
		this.var = var;
	}
	
	
	public SCVPString() {
		structure = "";
		constants = new ArrayList<String>();
		occs = new ArrayList<String>();
		position = new Position();
	}
	
	public void setIpOccs(List<String> ipOccs) {
		this.ipOccs = ipOccs;
	}
	public void addIpOccs(String ipocc) {
		if (ipOccs == null)
			ipOccs = new ArrayList<String>();
		ipOccs.add(ipocc);
	}
	
	public List<String> getIpOcc() {
		return ipOccs;
	}
	
	public String getStructure() {
		return structure;
	}
	public void setStructure(String structure) {
		this.structure = structure;
	}
	public List<String> getConstants() {
		return constants;
	}
	public void setConstants(List<String> constants) {
		this.constants = constants;
	}
	public List<String> getOccs() {
		return occs;
	}
	public void setOccs(List<String> variables) {
		this.occs = variables;
	}
	public Position getPosition() {
		return position;
	}
	public void setPosition(Position position) {
		this.position = position;
	}
	@Override
	public String toString() {
//		return var +" [structure=" + structure + ", constants=" + constants + ", occs=" + occs + ", position="
//				+ position + "]";
		return "[structure=" + structure + ", constants=" + constants + ", occs=" + occs + ", position="
		+ position + "]";//modify by JJL, 去掉变量
	}
	
	public String replaceString() {
		return "[structure=" + structure + ", constants=" + constants + ", occs=" + occs + ", position="
				+ position + "]";
	}
}
