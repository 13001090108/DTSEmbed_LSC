package softtest.symboltable.c.Type;

import java.util.*;

public class CType_BaseType extends CType {

	public static final CType_BaseType boolType = new CType_BaseType("bool");
	public static final CType_BaseType BoolType = new CType_BaseType("_Bool");
	public static final CType_BaseType intType = new CType_BaseType("int");
	public static final CType_BaseType uIntType = new CType_BaseType("unsigned int");
	public static final CType_BaseType charType = new CType_BaseType("char");
	public static final CType_BaseType signedCharType = new CType_BaseType("signed char");
	public static final CType_BaseType uCharType = new CType_BaseType("unsigned char");
	//public static final CType_BaseType wcharType = new CType_BaseType("wchar_t");
	public static final CType_BaseType doubleType = new CType_BaseType("double");
	public static final CType_BaseType longDoubleType = new CType_BaseType("long double");
	public static final CType_BaseType floatType = new CType_BaseType("float");
	public static final CType_BaseType longType = new CType_BaseType("long");
	public static final CType_BaseType uLongType = new CType_BaseType("unsigned long");
	public static final CType_BaseType longLongType = new CType_BaseType("long long");
	public static final CType_BaseType uLongLongType = new CType_BaseType("unsigned long long");
	public static final CType_BaseType shortType = new CType_BaseType("short");
	public static final CType_BaseType uShortType = new CType_BaseType("unsigned short");
	public static final CType_BaseType voidType = new CType_BaseType("void");
	public static final CType_BaseType bitType = new CType_BaseType("bit");
	public static final CType_BaseType sbitType = new CType_BaseType("sbit");
	public static final CType_BaseType sfrType = new CType_BaseType("sfr");
	public static final CType_BaseType sfr16Type = new CType_BaseType("sfr16");
	
	public CType_BaseType() {
		
	}
	
	public CType_BaseType(String name) {
		this.name = name;
	}
	
	@Override
	public boolean isBasicType(){
		return true;
	}
	
	public boolean isUnSigned() {
		return name.contains("unsigned");
	}
	
	public boolean isIntegerType(){
		if(name.contains("float")||name.contains("double")){
			return false;
		}else{
			return true;
		}
	}
	
	public static CType getBaseType(String name) {
		HashSet<String> set=new HashSet<String>();
		String types[]=name.split(" ");
		for(String type:types){
			if(type.equals("long")&&set.contains("long")){
				set.add("long2");
			}else{
				set.add(type);
			}
		}
		
		if(set.contains("bool")){
			return boolType;
		}else if(set.contains("_Bool")){
			return BoolType;
		}else if(set.contains("void")){
			return voidType;
		}else if(set.contains("float")){
			return floatType;
		}else if(set.contains("double") || set.contains("DOUBLE")){
			if(set.contains("long")){
				return longDoubleType;
			}else{
				return doubleType;
			}
		}else if(set.contains("long")){
			if(set.contains("long2")){
				if(set.contains("unsigned")){
					return uLongLongType;
				}else{
					return longLongType;
				}
			}else{
				if(set.contains("unsigned")){
					return uLongType;
				}else{
					return longType;
				}
			}
		}else if(set.contains("int") || set.contains("INTEGER")){
			if(set.contains("unsigned")){
				return uIntType;
			}else{
				return intType;
			}
		}else if(set.contains("short")){
			if(set.contains("unsigned")){
				return uShortType;
			}else{
				return shortType;
			}
		}else if(set.contains("char")){
			if(set.contains("unsigned")){
				return uCharType;
			}else if(set.contains("signed")){
				return signedCharType;
			}else{
				return charType;
			}
		}else if(set.contains("unsigned")){
			return uIntType;
		}else if(set.contains("signed")){
			return intType;
		}else if(set.contains("bit")){
			return bitType;
		}else if(set.contains("sbit")){
			return sbitType;
		}else if(set.contains("sfr")){
			return sfrType;
		}else if(set.contains("sfr16")){
			return sfr16Type;
		}else if(set.contains("POINTER")){
			return CType_Pointer.VOID;//2010.9.15 zys 暂时将指针类型转换为VOID指针
		}
		throw new RuntimeException("Unknown base type!");
	}
	
	@Override
	public int getSize() {
		int size = softtest.config.c.Config.INT_SIZE;
		if (this == CType_BaseType.boolType || this == CType_BaseType.charType || this == CType_BaseType.uCharType) {
			size = 1;
		} else if (this == CType_BaseType.doubleType || this == CType_BaseType.longLongType || this == CType_BaseType.longDoubleType) {
			size = 8;
		} else if (this == CType_BaseType.uShortType || this == CType_BaseType.shortType ) {
			size = 2;
		}else if(name.startsWith("bit:")){
			//处理为一个字节
			size=1;
		}
		return size;
	}
}
