package softtest.scvp.c;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;


import softtest.ast.c.ASTConstant;
import softtest.ast.c.SimpleNode;
import softtest.symboltable.c.NameOccurrence;


public class SCVP {
	/**
	 * @author cmershen
	 */
	public NameOccurrence occ;
	private String structure; //s
	private List<? super ASTConstant> constants; //c
	//private List<SimpleNode> variables; //v
	private HashSet<NameOccurrence> occs;//occs
	private Position position; //p
	public String getStructure() {
		return structure;
	}
	public void setStructure(String structure) {
		this.structure = structure;
	}
	public List<? super ASTConstant> getConstants() {
		return constants;
	}
	public String getConstants2() {
		String ans="[";
		for(int i=0;i<constants.size();i++) {
			ASTConstant ast = (ASTConstant)(constants.get(i));
			ans+=ast.getImage();
			if(i!=constants.size()-1)
				ans+=",";
			
		}
		
		ans+="]";
		return ans;
	}
	public void setConstants(List<? super ASTConstant> constants) {
		this.constants = constants;
	}
	public Position getPosition() {
		return position;
	}
	public void setPosition(Position position) {
		this.position = position;
	}
	public SCVP() {
		this.occ=null;
		this.constants = new ArrayList<SimpleNode>();
		//this.variables = new ArrayList<SimpleNode>();
		this.occs = new HashSet<NameOccurrence>();
		this.position = new Position();
	}
	public void printSCVPtoFile(String fileName) {
		try {
			FileWriter fw = new FileWriter(fileName,true);
			StringBuffer sb = new StringBuffer();
			sb.append("SCVP of "+occ.toString()+"\n");
			sb.append("structure=\t"+structure+"\n");
			sb.append("constants=\t");
			if(constants!=null) {
				if(constants.size()==0)
					sb.append("null\n");
					
				else {
					for(int i=0;i<constants.size();i++) {
						sb.append(((ASTConstant)constants.get(i)).getImage());
						if(i!=constants.size()-1)
							sb.append(" ");
						else
							sb.append("\n");
					}
				}
			}
			else
				sb.append("null\n");
			sb.append("occs=\t");
			if(occs!=null) {
				if(occs.size()==0)
					sb.append("null\n");
				else {
					sb.append(occs+"\n");
				}
			}
			else
				sb.append("null\n");
			sb.append(position+"\n");
			fw.write(sb.toString());
			fw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	@Override
	public String toString() {
		String ans="\n";
		if(occ!=null)
			ans+=("SCVP of "+occ.toString()+"\n");
		ans+=("structure=\t"+structure+"\n");
		ans+=("constants=\t");
		if(constants!=null) {
			if(constants.size()==0)
				ans+=("null\n");
				
			else {
				for(int i=0;i<constants.size();i++) {
					ans+=(((ASTConstant)constants.get(i)).getImage());
					if(i!=constants.size()-1)
						ans+=(" ");
					else
						ans+=("\n");
				}
			}
		}
		else
			ans+=("null\n");
		ans+=("occs=\t");
		if(occs!=null) {
			if(occs.size()==0)
				ans+=("null\n");
			else {
				ans+=(occs+"\n");
			}
		}
		else
			ans+=("null\n");
		ans+=(position+"\n");
		return ans;
	}
	
	public void printSCVP() {
		if(occ!=null)
			System.out.println("SCVP of "+occ.toString());
		System.out.println("structure=\t"+structure);
		System.out.print("constants=\t");
		if(constants!=null) {
			if(constants.size()==0)
				System.out.println("null");
				
			else {
				for(int i=0;i<constants.size();i++) {
					System.out.print(((ASTConstant)constants.get(i)).getImage());
					if(i!=constants.size()-1)
						System.out.print(" ");
					else
						System.out.println();
				}
			}
		}
		else
			System.out.println("null");
//		System.out.print("variable=\t");
//		if(variables!=null) {
//			if(variables.size()==0)
//				System.out.println("null");
//			else {
//				for(int i=0;i<variables.size();i++) {
//					System.out.print(((SimpleNode)variables.get(i)).getImage());
//					if(i!=variables.size()-1)
//						System.out.print(" ");
//					else
//						System.out.println();
//				}
//			}
//		}
//		else
//			System.out.println("null");
		System.out.print("occs=\t");
		if(occs!=null) {
			if(occs.size()==0)
				System.out.println("null");
			else {
				System.out.println(occs);
			}
		}
		else
			System.out.println("null");
		System.out.println(position);
	}
	public HashSet<NameOccurrence> getOccs() {
		return occs;
	}
	public void setOccs(HashSet<NameOccurrence> occs) {
		this.occs = occs;
	}
	public NameOccurrence getOcc() {
		return occ;
	}
	public void setOcc(NameOccurrence occ) {
		this.occ = occ;
	}
	public SCVPString convertToString() {
		SCVPString ret = new SCVPString();
		//S
		if (occ != null){
			ret.setVar(occ.getImage());
		}else{
			ret.setVar("unknow");
		}
		ret.setStructure(structure);
		//C
		List<String> newConst = new ArrayList<String>();
		if(constants!=null) {
			for(Object c:constants)
				if(c instanceof ASTConstant)
					newConst.add(((ASTConstant)c).getImage());
		}
		ret.setConstants(newConst);
		//V
		List<String> newOccs = new ArrayList<String>();
		for(NameOccurrence occ:occs)
			newOccs.add(occ.toString());
		ret.setOccs(newOccs);
		ret.setPosition(position);
		return ret;
	}
}
