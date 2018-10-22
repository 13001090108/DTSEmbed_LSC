package softtest.symboltable.c.Type;

import java.util.ArrayList;
import java.util.List;

public class CType_Function extends CType {
	
	private CType returntype;
	
	private ArrayList<CType> argTypes = new ArrayList<CType>();

	private boolean isVarArg = false;
	
	
	public CType_Function() {
	}
		
	public CType_Function(String name) {
		super(name);
	}
	
	public void setIsVarArg(boolean isVarArg) {
		this.isVarArg = isVarArg;
	}
	
	public boolean isVarArg() {
		return isVarArg;
	}
	
	public ArrayList<CType> getArgTypes() {
		return argTypes;
	}
	
	public boolean addArgType(CType type) {
		try {
			argTypes.add(type);
			return true;
		} catch (Exception e) {
			return false;
		}
	}

	public boolean addArgType(CType[] types) {
		try {
			if (types != null && types.length > 0) {
				for (int i = 0; i < types.length; i++) {
					argTypes.add(types[i]);
				}
				return true;
			}
			return false;
		} catch (Exception e) {
			return false;
		}
	}

	public ArrayList<CType> setArgTypes(ArrayList<CType> types) {
		argTypes = types;
		return argTypes;
	}

	@Override
	public String toString() {
		String name="";
		name = this.name + "(";
		if (argTypes != null && argTypes.size() > 0) {
			for (int i = 0; i < argTypes.size() - 1; i++) {
				name = name + argTypes.get(i) + ",";
			}
			name += argTypes.get(argTypes.size() - 1);
			if (isVarArg) {
				name += ",...";
			} 
			name=name + ")";
		}else{
			if (isVarArg) {
				name += "...";
			} 
			name=name + ")";
		}
		if(returntype==null){
			name=name+"int";
		}else{
			name= name+returntype.toString();
		}
		return name;
	}

	public CType getReturntype() {
		return returntype;
	}

	public void setReturntype(CType returntype) {
		this.returntype = returntype;
	}
	
	public CType getOriginaltype() {
		return returntype;
	}

	public void setOriginaltype(CType originalType) {
		returntype = originalType;
	}

	@Override
	public int getSize() {
		return 4;
	}
}
