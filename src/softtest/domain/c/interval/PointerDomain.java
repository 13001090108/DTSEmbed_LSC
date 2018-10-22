package softtest.domain.c.interval;

import java.util.HashSet;


import softtest.config.c.Config;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.domain.c.interval.IntegerDomain;
import softtest.symboltable.c.Type.*;
import softtest.symboltable.c.VariableNameDeclaration;

public class PointerDomain extends Domain {
	//zys:2010.8.11	记录区间变量在运算时是否为减法特性
	private boolean isMinus=false;
	CType elementtype;
	Expression length;
	PointerValue value;
	
	//add by zhouhb
	//标识指针偏移量范围
	public IntegerDomain offsetRange;
	//标识指向空间有效值长度
	public IntegerDomain allocRange;
    //用于标识指针指向空间分配类型。空指针为NUll，指针未初始化为NotNull
//    public CType AllocType=CType_AllocType.Unkown; 
//    //用于标识指针指向空间分配类型汇聚后的具体信息。
    //add by zhouhb 2010/8/31
    public HashSet<CType_AllocType> Type;
    //标识抽象空间名称，和offsetRange一同描述抽象空间
    public String name;
	//存储空间上的真实值，暂时未做值关联
	public Domain realDomain;
	//别名集合，用于记录别名信息
	public HashSet<VariableNameDeclaration>VariableInMemory=new HashSet<VariableNameDeclaration>();
	//抽象空间上变量集合
	public HashSet<VariableNameDeclaration>Alias=new HashSet<VariableNameDeclaration>();
	
	
	public PointerDomain() {
		elementtype=CType_BaseType.getBaseType("void");
		domaintype=DomainType.POINTER;
		value=PointerValue.UNKOWN;
		offsetRange=new IntegerDomain(IntegerDomain.DEFAULT_MIN,IntegerDomain.DEFAULT_MAX);
		allocRange=new IntegerDomain(0,0);
		Type=new HashSet();
	}
	
	public PointerDomain(PointerValue value){
		this();
		this.value=value;
	}
	/**
	 * 得到一个指针型未知区间
	 * 
	 * @return 一个指针型未知区间
	 */
	public static PointerDomain getUnknownDomain() {
		PointerDomain r = new PointerDomain(PointerValue.UNKOWN);
		r.setUnknown(true);
		r.Type.add(CType_AllocType.heapType);
		return r;
	}
	public CType getElementtype() {
		return elementtype;
	}

	public void setElementtype(CType elementtype) {
		this.elementtype = elementtype;
	}

	public Expression getLength() {
		return length;
	}

	public Expression getSize(){
		Expression ret=null;
		if(length==null||elementtype==null){
			ret =new Expression(SymbolFactor.genSymbol(CType_BaseType.getBaseType("int")));
		}else{
			ret=length.mul(new Expression(elementtype.getSize()));
		}
		return ret;
	}
	
	public void setLength(Expression length) {
		this.length = length;
	}

	public PointerValue getValue() {
		return value;
	}

	public void setValue(PointerValue value) {
		this.value = value;
	}

	//获取空间长度
	public long getLen(PointerDomain d){
		long Len=0;
		//temp用于存放每个空间的长度
		long temp;
		for (IntegerInterval range : d.offsetRange.intervals) {
			temp=range.getMax()-range.getMin()+1;
			if(temp>Len)
				Len=temp;
		}
		return Len;	
	}
	
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		if(unknown)
			return "unknown";
		else{
			String result = " " + "offsetRange: "+ ((offsetRange != null) ? offsetRange.toString() : "");
			result = result + " " + "Eval: "+ ((allocRange!=null)? allocRange.toString(): "");
			result = result +" "+"Type:"+ Type.toString();
			if(value==PointerValue.NULL){
				return "NULL"+result;
			}else if(value==PointerValue.NULL_OR_NOTNULL){
				return "NULL_OR_NOTNULL"+result;
			}else if(value==PointerValue.EMPTY){
				return "EMPTY"+result;
			}else if(value==PointerValue.UNKOWN){
				return "UNKOWN"+result;
			}else {
//				b.append("&");
//				b.append(elementtype.toString());
//				b.append("(");
//				b.append(length);
//				b.append(")");
				return "NOTNULL"+result;
				//return b.toString()+result;
			}
		}
		//暂时不做别名分析，待CPP通过测试后再添加相应处理
//		result = result +" "+"Memory:"+ name;
//		result = result +" "+"Alias:"+Name(Alias);
//		result = result +" "+"VariableInMemory:"+Name(VariableInMemory);
	}
	
	@Override
	public Domain clone() throws CloneNotSupportedException {
		PointerDomain domain=(PointerDomain)super.clone();
		domain.elementtype=elementtype;
		domain.length=length;
		domain.value=value;
		domain.Type=Type;
		return domain;
	}
	public static PointerDomain add(PointerDomain pointdomain, IntegerDomain i) {
		if(pointdomain.unknown)
			return PointerDomain.getUnknownDomain();
		PointerDomain result;
		try{
		result = (PointerDomain)pointdomain.clone();
		result.offsetRange=IntegerDomain.sub(result.offsetRange, i);
		}
		catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		return result;
	}
	
	public static PointerDomain sub(PointerDomain pointdomain, IntegerDomain i) {
		if(pointdomain.unknown)
			return PointerDomain.getUnknownDomain();
		PointerDomain result;
		try{
		result = (PointerDomain)pointdomain.clone();
		result.offsetRange=IntegerDomain.add(result.offsetRange, i);
		}
		catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		return result;
	}
	
	public static PointerDomain inverse(PointerDomain a) {
		PointerDomain ret= null;
		try {
			ret= (PointerDomain)a.clone();
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException(e);
		}
		if(a.unknown)
			return ret;
		switch(ret.value){
		case NULL:
			ret.value=PointerValue.NOTNULL;
			break;
		case EMPTY:
			ret.value=PointerValue.NULL_OR_NOTNULL;
			break;
		case NULL_OR_NOTNULL:
			ret.value=PointerValue.EMPTY;
			break;
		case NOTNULL:
			ret.value=PointerValue.NULL;
			break;
		}
		//由于指针模型关联区间，原有的符号运算不能满足现有需求，故做如下修改
		//赋值区间修改不精确，有待修改
		//modified by zhouhb 2010/7/19
		ret.offsetRange=IntegerDomain.inverse(a.offsetRange);
		//ret.AllocType=ret.AllocTypeInverse(a.AllocType);
		ret.Type=ret.TypeInverse(a.Type);
		return ret;
	}
	
	public static PointerDomain intersect(PointerDomain a,PointerDomain b){
		if(a.unknown || a.getValue()==PointerValue.UNKOWN)
			return (PointerDomain) b.copy();
		if(b.unknown || b.getValue()==PointerValue.UNKOWN)
			return (PointerDomain) a.copy();
		PointerDomain ret= new PointerDomain();
		ret.setElementtype(ret.getElementtype());
		Expression e1=a.getLength();
		Expression e2=b.getLength();
		ret.setLength(e1!=null?e1:e2);
		
		if(a.getValue()==b.getValue()){
			ret.setValue(a.getValue());
		}else if(a.getValue()==PointerValue.NULL_OR_NOTNULL){
			ret.setValue(b.getValue());
		}else if(b.getValue()==PointerValue.NULL_OR_NOTNULL){
			ret.setValue(a.getValue());
		}else {
			ret.setValue(PointerValue.EMPTY);
		}
		//由于指针模型关联区间，原有的符号运算不能满足现有需求，故做如下修改
		//modified by zhouhb 2010/7/19
		ret.offsetRange=IntegerDomain.intersect(a.offsetRange, b.offsetRange);
		ret.allocRange=IntegerDomain.intersect(a.allocRange, b.allocRange);
		if(ret.value.toString().equals("NULL")){
			//ret.AllocType=CType_AllocType.Null;
			ret.Type.add(CType_AllocType.Null);
		}else{
			//ret.AllocType=ret.AllocTypeIntersect(a.AllocType, b.AllocType);
			ret.Type=ret.TypeIntersect(a.Type, b.Type);
		}
		return ret;
	}
	
	public static PointerDomain union(PointerDomain a,PointerDomain b){
		PointerDomain ret= new PointerDomain();
		ret.setElementtype(ret.getElementtype());
		Expression e1=a.getLength();
		Expression e2=b.getLength();
		ret.setLength(e1!=null?e1:e2);
		
		if (Config.DOMAIN_CONSERVATIVE) {
			if (a.unknown || b.unknown) {
				ret = PointerDomain.getUnknownDomain();
				return ret;
			}
		} else {
			if (a.unknown) {
				if (!b.unknown && b.value == PointerValue.NOTNULL) {
					// notnull与unknown 求并取unknown
					ret = PointerDomain.getUnknownDomain();
				} else {
					ret = (PointerDomain) b.copy();
				}
				return ret;
			}
			if (b.unknown) {
				if (!a.unknown && a.value == PointerValue.NOTNULL) {
					// notnull与unknown 求并取unknown
					ret = PointerDomain.getUnknownDomain();
				} else {
					ret = (PointerDomain) a.copy();
				}
				return ret;
			}
		}
		
		if(a.getValue()==b.getValue()){
			ret.setValue(a.getValue());
		}else if(a.getValue()==PointerValue.EMPTY){
			ret.setValue(b.getValue());
		}else if(b.getValue()==PointerValue.EMPTY){
			ret.setValue(a.getValue());
		}else{
			ret.setValue(PointerValue.NULL_OR_NOTNULL);
		}
		try{
		if (a.offsetRange == null && b.offsetRange != null)
			ret.offsetRange = b.offsetRange.clone();
		else if (b.offsetRange == null && a.offsetRange != null)
			ret.offsetRange= a.offsetRange.clone();
		else if (b.offsetRange == null && a.offsetRange == null)
			ret.offsetRange=null;
		else ret.offsetRange=IntegerDomain.union(a.offsetRange,b.offsetRange);
		
		if (a.allocRange == null && b.allocRange != null)
			ret.allocRange = b.allocRange.clone();
		else if (b.allocRange == null && a.allocRange != null)
			ret.allocRange = a.allocRange.clone();
		else if (b.allocRange == null && a.allocRange == null)
			ret.allocRange = null;
		else ret.allocRange=IntegerDomain.union(a.allocRange,b.allocRange);
		
		//ret.AllocType=AllocTypeUnion(a.AllocType,b.AllocType);
		ret.Type=TypeUnion(a.Type,b.Type);
		}catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		return ret;
	} 
	
//	public static CType AllocTypeUnion(CType a,CType b){
//		CType result;
//		if(a.equals(CType_AllocType.heapType)){
//			if(b.equals(CType_AllocType.heapType))
//				result=a;
//			else if(b.equals(CType_AllocType.stackType)||b.equals(CType_AllocType.staticType)||b.equals(CType_AllocType.NotNull))
//				result=CType_AllocType.NotNull;
//			else
//				result=CType_AllocType.Unkown;
//		}else if(a.equals(CType_AllocType.stackType)){
//			if(b.equals(CType_AllocType.stackType))
//				result=a;
//			else if(b.equals(CType_AllocType.heapType)||b.equals(CType_AllocType.staticType)||b.equals(CType_AllocType.NotNull))
//				result=CType_AllocType.NotNull;
//			else 
//				result=CType_AllocType.Unkown;
//		}else if(a.equals(CType_AllocType.staticType)){
//			if(b.equals(CType_AllocType.staticType))
//				result=a;
//			else if(b.equals(CType_AllocType.heapType)||b.equals(CType_AllocType.stackType)||b.equals(CType_AllocType.NotNull))
//				result=CType_AllocType.NotNull;
//			else 
//				result=CType_AllocType.Unkown;
//		}else if(a.equals(CType_AllocType.Null)){
//			if(b.equals(CType_AllocType.Null))
//				result=a;
//			else 
//				result=CType_AllocType.Unkown;
//		}else if(a.equals(CType_AllocType.NotNull)){
//			if(b.equals(CType_AllocType.NotNull))
//				result=a;
//			else if(b.equals(CType_AllocType.heapType)||b.equals(CType_AllocType.staticType)||b.equals(CType_AllocType.stackType)||b.equals(CType_AllocType.NotNull))
//				result=CType_AllocType.NotNull;
//			else 
//				result=CType_AllocType.Unkown;
//		}else if(a.equals(CType_AllocType.Empty)){
//			if(b.equals(CType_AllocType.Empty))
//				result=a;
//			else
//				result=CType_AllocType.Unkown;
//		}else
//			result=CType_AllocType.Unkown;
//		return result;
//	}

//	public static CType AllocTypeIntersect(CType a,CType b){
//		CType result;
//		if(a.equals(CType_AllocType.heapType)){
//			if(b.equals(CType_AllocType.heapType)||b.equals(CType_AllocType.NotNull)||b.equals(CType_AllocType.Unkown))
//				result=a;
//			else
//				result=CType_AllocType.Empty;
//		}else if(a.equals(CType_AllocType.stackType)){
//			if(b.equals(CType_AllocType.stackType)||b.equals(CType_AllocType.NotNull)||b.equals(CType_AllocType.Unkown))
//				result=a;
//			else 
//				result=CType_AllocType.Empty;
//		}else if(a.equals(CType_AllocType.staticType)){
//			if(b.equals(CType_AllocType.staticType)||b.equals(CType_AllocType.NotNull)||b.equals(CType_AllocType.Unkown))
//				result=a;
//			else 
//				result=CType_AllocType.Empty;
//		}else if(a.equals(CType_AllocType.Null)){
//			if(b.equals(CType_AllocType.Null)||b.equals(CType_AllocType.Unkown))
//				result=a;
//			else 
//				result=CType_AllocType.Empty;
//		}else if(a.equals(CType_AllocType.NotNull)){
//			if(b.equals(CType_AllocType.NotNull)||b.equals(CType_AllocType.Unkown))
//				result=a;
//			else if(b.equals(CType_AllocType.heapType)||b.equals(CType_AllocType.staticType)||b.equals(CType_AllocType.stackType))
//				result=b;
//			else 
//				result=CType_AllocType.Empty;
//		}else if(a.equals(CType_AllocType.Unkown)){
//			result=b;
//		}else
//			result=CType_AllocType.Empty;
//		return result;
//	}
	
//	public static CType AllocTypeInverse(CType a){
//		CType result;
//		if(a.equals(CType_AllocType.heapType)||a.equals(CType_AllocType.stackType)||a.equals(CType_AllocType.staticType)||a.equals(CType_AllocType.NotNull)){
//			result=CType_AllocType.Null;
//		}else if(a.equals(CType_AllocType.Null)){
//				result=CType_AllocType.NotNull;
//		}else if(a.equals(CType_AllocType.Unkown)){
//				result=CType_AllocType.Empty;
//		}else 
//			result=CType_AllocType.Unkown;
//		return result;
//	}
	
	public static HashSet<CType_AllocType> TypeUnion(HashSet<CType_AllocType> a,HashSet<CType_AllocType> b){
		HashSet<CType_AllocType> result=(HashSet<CType_AllocType>)a.clone();
		for(CType_AllocType type:b){
			result.add(type);
		}
		return result;
	}
	
	//分配类型求交进一步求精
	//modified by zhouhb 2010/10/19
	public static HashSet<CType_AllocType> TypeIntersect(HashSet<CType_AllocType> a,HashSet<CType_AllocType> b){
		HashSet<CType_AllocType> result=new HashSet();
		if(!a.isEmpty()){
			if(a.contains(CType_AllocType.NotNull)&&b.contains(CType_AllocType.NotNull))
				for(CType_AllocType type:a){
					if(b.contains(type)){
						result.add(type);
					}
				}
			else if(a.contains(CType_AllocType.NotNull))
				result=b;
			else if(b.contains(CType_AllocType.NotNull))
				result=a;
			else
				result=b;
		}
		return result;
	}
	
	//分配类型求反进一步求精
	//modified by zhouhb 2010/10/19
	public static HashSet<CType_AllocType> TypeInverse(HashSet<CType_AllocType> a){
		HashSet<CType_AllocType> result=(HashSet<CType_AllocType>)a.clone();
		if(result.contains(CType_AllocType.stackType)){
			result.remove(CType_AllocType.stackType);
			result.add(CType_AllocType.Null);
		}
		if(result.contains(CType_AllocType.heapType)){
			result.remove(CType_AllocType.heapType);
			result.add(CType_AllocType.Null);
		}
		if(result.contains(CType_AllocType.staticType)){
			result.remove(CType_AllocType.staticType);
			result.add(CType_AllocType.Null);
		}
		if(result.contains(CType_AllocType.Null)){
			result.remove(CType_AllocType.Null);
			result.add(CType_AllocType.NotNull);
		}
		return result;
	}

	public static PointerDomain getEmptyDomain(){
		PointerDomain ret=new PointerDomain();
		ret.value=PointerValue.EMPTY;
		return ret;
	}
	
	public static PointerDomain getFullDomain(){
		PointerDomain ret=new PointerDomain();
		ret.value=PointerValue.NULL_OR_NOTNULL;
		return ret;
	}
	
	public static PointerDomain getNullDomain(){
		PointerDomain ret=new PointerDomain();
		ret.value=PointerValue.NULL;
		return ret;
	}
	
	@Override
	public boolean isCanonical() {
		if (unknown) {
			return false;
		}
		if(value==PointerValue.NULL){
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int PRIME = 31;
		int result = 1;
		if (unknown) {
			return result;
		}
		result = PRIME * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final PointerDomain other = (PointerDomain) obj;
		if(this.unknown && other.unknown)
			return true;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}
	//方便控制流图中表示
	public HashSet<String> Name(HashSet<VariableNameDeclaration> Variable){
		HashSet<String> result=new HashSet<String>();
		for(VariableNameDeclaration v:Variable){
			result.add(v.getImage());
		}
		return result;
	}
	
	//CPP版：由于NULL预编译后为0，故需区分0所对应的是空指针还是常量0
	//暂时不做处理
//	private boolean IsNullPoint(ASTConstant node, Object data){
//			
//		
//	}
	private HashSet<VariableNameDeclaration> aliasMerge(HashSet<VariableNameDeclaration>Alias1,HashSet<VariableNameDeclaration>Alias2){
		for(VariableNameDeclaration name:Alias1){
			if(!Alias2.contains(name))
				Alias2.add(name);
		}
		for(VariableNameDeclaration v:Alias2){
			Domain domain =v.getDomain();
			((PointerDomain)domain).Alias=Alias2;
			v.setDomain(domain);
		}
		return Alias2;
	}
	private HashSet<VariableNameDeclaration> VariableInMemoryMerge(HashSet<VariableNameDeclaration>v1,HashSet<VariableNameDeclaration>v2){
		for(VariableNameDeclaration name:v1){
			if(!v2.contains(name))
				v2.add(name);
		}
		for(VariableNameDeclaration v:v2){
			Domain domain =v.getDomain();
			((PointerDomain)domain).VariableInMemory=v2;
			v.setDomain(domain);
		}
		return v2;
	}
	
	//用来检查间接别名
	private boolean IsAlias(VariableNameDeclaration v1,VariableNameDeclaration v2){
		if(((PointerDomain)v1.getDomain()).name==((PointerDomain)v2.getDomain()).name&&
				((PointerDomain)v1.getDomain()).offsetRange.equals(((PointerDomain)v2.getDomain()).offsetRange))
			return true;
		else
			return false;
		
	}
	public static PointerDomain valueOf(String str) {
		PointerValue value = PointerValue.valueOf(str);
		return new PointerDomain(value);
	}

	public boolean isMinus() {
		return isMinus;
	}

	public void setMinus(boolean isMinus) {
		this.isMinus = isMinus;
	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Domain intersect(Domain rDomain) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Domain subtract(Domain rDomain) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Domain union(Domain rDomain) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Domain unionwithUnkown(Domain rDomain) {
		// TODO Auto-generated method stub
		return null;
	}
}
