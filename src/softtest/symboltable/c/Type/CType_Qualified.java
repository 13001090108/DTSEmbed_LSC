package softtest.symboltable.c.Type;

import java.util.*;

public class CType_Qualified extends CType {
	HashSet<String> qualifiers=new HashSet<String>();
	
	public CType_Qualified(CType originaltype) {
		this.originaltype = originaltype;
		name="Qualified type";
	}
	
	private CType originaltype;

	public CType getOriginaltype() {
		return originaltype;
	}

	public void setOriginaltype(CType originaltype) {
		this.originaltype = originaltype;
	}
	@Override
	public boolean isPointType(){
		if (originaltype == null) {
			return false;
		}
		return originaltype.isPointType();
	}
	
	@Override
	public boolean isArrayType(){
		if (originaltype == null) {
			return false;
		}
		return originaltype.isArrayType();
	}
	
	@Override
	public boolean isBasicType(){
		if(originaltype!=null)
			return originaltype.isBasicType();
		return false;
	}
	
	@Override
	public boolean isClassType(){
		if(originaltype != null) {
			return originaltype.isClassType();
		}
		return false;
	}
	
	@Override
	public boolean isIntegerType(){
		if (originaltype == null) {
			return false;
		}
		return originaltype.isIntegerType();
	}
	
	@Override
	public CType getSimpleType() {
		if (originaltype != null) {
			return originaltype.getSimpleType();
		}
		return null;
	}
	
	@Override
	public int getSize() {
		if (originaltype == null) {
			return softtest.config.c.Config.INT_SIZE;
		}
		return originaltype.getSize();
	}
	
	public void addQualifier(String qualifier){
		qualifiers.add(qualifier);
	}
	
	public void removeQualifier(String qualifier){
		qualifiers.remove(qualifier);
	}
	
	boolean isQualifiedBy(String qualifier){
		return  qualifiers.contains(qualifier);
	}
	
	@Override
	public String toString() {
		StringBuffer buf=new StringBuffer();
		List<String> list=new ArrayList<String>();
		list.addAll(qualifiers);
		Collections.sort(list);
		for(String s:list){
			buf.append(s+" ");
		}
		if(originaltype != null){
			buf.append(originaltype.toString());
		}
		return buf.toString();	
	}
}
