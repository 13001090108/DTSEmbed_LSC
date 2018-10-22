package softtest.domain.c.interval;

import java.util.TreeSet;

import softtest.config.c.Config;
import softtest.domain.c.symbolic.Expression;


import softtest.symboltable.c.Type.*;

public abstract class Domain implements Cloneable{
	public DomainType getDomaintype() {
		return domaintype;
	}

	public abstract String toString();
	
	public DomainType domaintype;
	
	/**
	 * unknown标记，代表当前区间是否未知
	 */
	protected boolean unknown = false;
	
	public Domain(){
		domaintype=DomainType.UNKNOWN;
	}
	
	@Override
	public Domain clone() throws CloneNotSupportedException {
		Domain domain=(Domain) super.clone();
		domain.unknown = this.unknown;
		domain.domaintype=domaintype;
		return domain;
	}
	
	public boolean isNumberDomain(){
		return (domaintype==DomainType.DOUBLE || domaintype==DomainType.INTEGER);
	}
	
	public static DoubleDomain castToDoubleDomain(Domain domain){
		return (DoubleDomain)castToType(domain,CType_BaseType.getBaseType("double"));
	}
	
	public static IntegerDomain castToIntegerDomain(Domain domain){
		return (IntegerDomain)castToType(domain,CType_BaseType.getBaseType("int"));
	}
	
	public static PointerDomain castToPointerDomain(Domain domain){
		return (PointerDomain)castToType(domain,new CType_Pointer());
	}
	
	/**
	 * 判断当前区间对象是否为未知区间
	 * 
	 * @return 返回unknown标记
	 */
	public boolean isUnknown() {
		return unknown;
	}
	
	/**
	 * 设置unknown标记
	 * 
	 * @param unknown
	 */
	public void setUnknown(boolean unknown) {
		this.unknown = unknown;
	}
	
	//xyf
	public abstract boolean isEmpty();
	
	public abstract Domain intersect(Domain rDomain);
	
	public abstract Domain subtract(Domain rDomain);
	
	public abstract Domain union(Domain rDomain);
	
	public abstract Domain unionwithUnkown(Domain rDomain);
	
	
	/**
	 * 复制当前区间对象
	 * 
	 * @return 当前区间对象的一个拷贝
	 */
	public Domain copy() {
		Domain ret = null;
		try {
			ret = (Domain) clone();
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException(e);
		}
		return ret;
	}
	
	public static Domain castToType(Domain domain,CType type){
		Domain ret=null;
		if(domain==null){
			return null;
		}
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			CType_AbstPointer pointertype = null;
			//liuli:对不同类型的type分开处理
			if(type instanceof CType_Function){
				CType_Function ftype = (CType_Function)type.getSimpleType();
				CType temp=ftype.getReturntype();
				if(temp instanceof CType_Typedef)
					pointertype=(CType_AbstPointer) temp.getNormalType();
				else
					pointertype=(CType_AbstPointer)ftype.getReturntype();
			}else if(type instanceof CType_AbstPointer){
				pointertype=(CType_AbstPointer)type.getSimpleType();
			}else if(type instanceof CType_Qualified){
				pointertype = (CType_AbstPointer)type.getSimpleType();				
			}else if(type instanceof CType_Typedef){
				pointertype = (CType_AbstPointer)type.getSimpleType();
			}
		
			CType eletype=pointertype.getOriginaltype();
			if(eletype==null){
				eletype=CType_BaseType.getBaseType("int");
			}
			PointerDomain todomain=new PointerDomain();
			switch(domain.domaintype){
			case POINTER:{
				PointerDomain fromdomain=(PointerDomain)domain;
				todomain.setElementtype(eletype);
				if(fromdomain.getLength()!=null){
					todomain.setLength(fromdomain.getLength().mul(new Expression((double)fromdomain.getElementtype().getSize()/eletype.getSize())));
				}
				break;
			}
			case DOUBLE:{
				DoubleDomain fromdomain=(DoubleDomain)domain;
				todomain.setElementtype(eletype);
				DoubleInterval interval=fromdomain.jointoOneInterval();
				if(interval.contains(0)){
					if(interval.isCanonical()){
						todomain.value=PointerValue.NULL;
					}else{
						todomain.value=PointerValue.NULL_OR_NOTNULL;
					}
				}
				break;
			}
			case INTEGER:{
				IntegerDomain fromdomain=(IntegerDomain)domain;
				todomain.setElementtype(eletype);
				IntegerInterval interval=fromdomain.jointoOneInterval();
				if(interval.contains(0)){
					if(interval.isCanonical()){
						todomain.value=PointerValue.NULL;
						//修改了空指针条件判断的区间转化
						//modified by zhouhb 2010/8/17
						todomain.offsetRange.intervals.clear();
						//todomain.AllocType=CType_AllocType.Null;	
						todomain.Type.add(CType_AllocType.Null);
					}else{
						todomain.value=PointerValue.NULL_OR_NOTNULL;
					}
				}
				break;
			}
			}
			if(domain instanceof PointerDomain)
				ret=domain;
			else
				ret=todomain;
			break;
		}
		case INTEGER:{
			IntegerDomain todomain=null;
			switch(domain.domaintype){
			case POINTER:{
				PointerDomain fromdomain=(PointerDomain)domain;
				switch(fromdomain.getValue()){
				case NULL:
					todomain=new IntegerDomain(0,0);
					break;
				case NOTNULL:
					todomain=new IntegerDomain(1,Long.MAX_VALUE);
					break;
				default:
					todomain=new IntegerDomain(0,Long.MAX_VALUE);
					break;
				}
				break;
			}
			case DOUBLE:{
				DoubleDomain d=(DoubleDomain)domain;
				TreeSet<IntegerInterval> intervals=new TreeSet<IntegerInterval>();
				for (DoubleInterval interval : d.getIntervals()) {
					intervals.add(new IntegerInterval(Math.round(interval.getMin()-0.5),Math.round(interval.getMax()-0.5)));
				}
				todomain=new IntegerDomain();
				todomain.setIntervals(intervals);
				todomain.setUnknown(d.isUnknown());
				break;
			}
			case INTEGER:{
				todomain=(IntegerDomain)domain;
				break;
			}
			}
			ret=todomain;
			break;
		}
		case DOUBLE:{
			DoubleDomain todomain=null;
			switch(domain.domaintype){
			case POINTER:{
				PointerDomain fromdomain=(PointerDomain)domain;
				switch(fromdomain.getValue()){
				case NULL:
					todomain=new DoubleDomain(0,0);
					break;
				case NOTNULL:
					todomain=new DoubleDomain(1,Double.POSITIVE_INFINITY);
					break;
				default:
					todomain=new DoubleDomain(0,Double.POSITIVE_INFINITY);
					break;
				}
				break;
			}
			case DOUBLE:{
				todomain=(DoubleDomain)domain;
				break;
			}
			case INTEGER:{
				IntegerDomain d=(IntegerDomain)domain;
				TreeSet<DoubleInterval> intervals=new TreeSet<DoubleInterval>();
				for (IntegerInterval interval : d.getIntervals()) {
					double min=(interval.getMin()==Long.MIN_VALUE)?Double.NEGATIVE_INFINITY:interval.getMin();
					double max=(interval.getMax()==Long.MAX_VALUE)?Double.POSITIVE_INFINITY:interval.getMax();
					intervals.add(new DoubleInterval(min,max));
				}
				todomain=new DoubleDomain();
				todomain.setIntervals(intervals);
				todomain.setUnknown(d.isUnknown());
				break;
			}
			}
			ret=todomain;
			break;
		}
		}
		return ret;
	}
	
	public static Domain inverse(Domain d){
		Domain ret = null;
		if (d == null) {
			return null;
		}
		try {
			switch (d.getDomaintype()) {
			case POINTER: {
				PointerDomain p1 = null;
				p1 = (PointerDomain) d.clone();
				ret = PointerDomain.inverse(p1);
				break;
			}
			case INTEGER: {
				IntegerDomain p1 = null;
				p1 = (IntegerDomain) d.clone();
				ret = IntegerDomain.inverse(p1);
				break;
			}
			case DOUBLE: {
				DoubleDomain p1 = null;
				p1 = (DoubleDomain) d.clone();
				ret = DoubleDomain.inverse(p1);
				break;
			}
			}
		} catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		return ret;
	}
	
	public static Domain intersect(Domain d1,Domain d2,CType type){
		Domain ret=null;
		try{			
			//end by zhouhb
			if(d1==null){
				ret = (d2==null)?null:(Domain)d2.clone();
				return ret;
			}
			if(d2==null){
				ret = (d1==null)?null:(Domain)d1.clone();
				return ret;
			}
			//add by zhouhb
			if(d1.isUnknown()){
				return d2;
			}
			
		}catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			PointerDomain p1=null,p2=null;
			p1=(PointerDomain)castToType(d1,type);
			p2=(PointerDomain)castToType(d2,type);
			ret=PointerDomain.intersect(p1, p2);
			break;
		}
		case INTEGER:{
			IntegerDomain i1=null,i2=null;
			i1=(IntegerDomain)castToType(d1,type);
			i2=(IntegerDomain)castToType(d2,type);
			ret=IntegerDomain.intersect(i1, i2);
			break;
		}
		case DOUBLE:{
			DoubleDomain i1=null,i2=null;
			i1=(DoubleDomain)castToType(d1,type);
			i2=(DoubleDomain)castToType(d2,type);
			ret=DoubleDomain.intersect(i1, i2);
			break;
		}
		}
		return ret;
	}
	
	public static Domain union(Domain d1,Domain d2,CType type){
		Domain ret=null;
		try{
			if(d1==null){
				ret = (d2==null)?null:(Domain)d2.clone();
				return ret;
			}
			if(d2==null){
				ret = (d1==null)?null:(Domain)d1.clone();
				return ret;
			}
		}catch (CloneNotSupportedException e) {
			e.printStackTrace();
			return null;
		}
		
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			PointerDomain p1=null,p2=null;
			p1=(PointerDomain)castToType(d1,type);
			p2=(PointerDomain)castToType(d2,type);
			ret=PointerDomain.union(p1, p2);
			break;
		}
		case INTEGER:{
			IntegerDomain i1=null,i2=null;
			i1=(IntegerDomain)castToType(d1,type);
			i2=(IntegerDomain)castToType(d2,type);
			ret=IntegerDomain.union(i1, i2);
			break;
		}
		case DOUBLE:{
			DoubleDomain i1=null,i2=null;
			i1=(DoubleDomain)castToType(d1,type);
			i2=(DoubleDomain)castToType(d2,type);
			ret=DoubleDomain.union(i1, i2);
			break;
		}
		}
		return ret;
	}
	
	public static Domain getEmptyDomainFromType(CType type){
		Domain ret=null;
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			PointerDomain p=new PointerDomain();
			CType eletype = null;
			//liuli:根据type的类型分开处理
			if(type instanceof CType_AbstPointer){
				CType_AbstPointer ptype=(CType_AbstPointer)type;
				eletype=ptype.getOriginaltype();
			}else if(type instanceof CType_Typedef){
				CType_Typedef ttype = (CType_Typedef)type;
				eletype=ttype.getOriginaltype();
			}
			
			if(eletype==null){
				eletype=CType_BaseType.getBaseType("int");
			}
			p.setElementtype(eletype);
			p.value=PointerValue.EMPTY;	
			ret=p;
			break;
		}
		case INTEGER:{
			ret=IntegerDomain.getEmptyDomain();
			break;
		}
		case DOUBLE:{
			ret=DoubleDomain.getEmptyDomain();
			break;
		}
		}
		return ret;
	}
	
	public static Domain substract(Domain d1,Domain d2,CType type){
		Domain ret=null;
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			PointerDomain p1=null,p2=null;
			p1=(PointerDomain)castToType(d1,type);
			p2=(PointerDomain)castToType(d2,type);
			ret=PointerDomain.intersect(p1,PointerDomain.inverse(p2));
			break;
		}
		case INTEGER:{
			IntegerDomain i1=null,i2=null;
			i1=(IntegerDomain)castToType(d1,type);
			i2=(IntegerDomain)castToType(d2,type);
			ret=IntegerDomain.intersect(i1, IntegerDomain.inverse(i2));
			break;
		}
		case DOUBLE:{
			DoubleDomain i1=null,i2=null;
			i1=(DoubleDomain)castToType(d1,type);
			i2=(DoubleDomain)castToType(d2,type);
			ret=DoubleDomain.intersect(i1, DoubleDomain.inverse(i2));
			break;
		}
		}
		return ret;
	}
	
	public static boolean isEmpty(Domain d) {
		if (d == null) {
			return false;
		}
		switch (d.getDomaintype()) {
		case POINTER: {
			PointerDomain p1 = null;
			p1 = (PointerDomain) d;
			if (p1.value == PointerValue.EMPTY) {
				return true;
			} else {
				return false;
			}
		}
		case INTEGER: {
			IntegerDomain p1 = null;
			p1 = (IntegerDomain) d;
			return p1.isEmpty();
		}
		case DOUBLE: {
			DoubleDomain p1 = null;
			p1 = (DoubleDomain) d;
			return p1.isEmpty();
		}
		}
		return false;
	}
	
	public static Domain getFullDomainFromType(CType type){
		Domain ret=null;
		switch(Domain.getDomainTypeFromType(type)){
		case POINTER:{
			PointerDomain p=new PointerDomain();
			CType_AbstPointer ptype=null;
			//liuli:type是返回值为指针的函数的处理
			if(type instanceof CType_Function){
				CType_Function ftype = (CType_Function)type.getSimpleType();
				CType temp=ftype.getReturntype();
				if(temp instanceof CType_Typedef)
					ptype=(CType_AbstPointer) temp.getNormalType();
				else
					ptype=(CType_AbstPointer)ftype.getReturntype();
			}else if(type instanceof CType_AbstPointer){
				ptype=(CType_AbstPointer)type.getSimpleType();
			}
						
			CType eletype=null;
			if(ptype!=null){
				eletype=ptype.getOriginaltype();
			}
			if(eletype==null){
				eletype=CType_BaseType.getBaseType("int");
			}
			p.setElementtype(eletype);
			//全集修改
			//modified by zhouhb 2011/2/25
			p.value=PointerValue.NULL_OR_NOTNULL;	
//			p.value=PointerValue.UNKOWN;	
//			p.setUnknown(true);
			ret=p;
			break;
		}
		case INTEGER:{
			ret=IntegerDomain.getFullDomain();
			break;
		}
		case DOUBLE:{
			ret=DoubleDomain.getFullDomain();
			break;
		}
		}
		return ret;
	}
	
	public static DomainType getDomainTypeFromType(CType type){
		if(type!=null){
			if(type.isPointType()){
				return DomainType.POINTER;
			}else if(type.isBasicType()){
				CType_BaseType basetype=(CType_BaseType)type.getSimpleType();
				if(basetype.isIntegerType()){
					return DomainType.INTEGER;
				}else{
					return DomainType.DOUBLE; 
				}
			}else if(type instanceof CType_Function){
				//zys:需要生成函数摘要，取得函数的返回值信息
				CType returnType=((CType_Function)type).getReturntype();
				return getDomainTypeFromType(returnType);
			}else if(type instanceof CType_BitField){
				return DomainType.INTEGER;
			}else if(type instanceof CType_Struct){
				//暂时弄成整型
				return DomainType.INTEGER;
			}else if(type instanceof CType_Union){
				//暂时弄成整型
				return DomainType.INTEGER;
			//liuli:处理typedef和enum
			}else if(type instanceof CType_Typedef){
				return DomainType.INTEGER;
			}else if(type instanceof CType_Enum){
				//暂时弄成整型
				return DomainType.INTEGER;
			}else if(type instanceof CType_Qualified){
				return DomainType.INTEGER;
			}
			throw new RuntimeException("illeage type!");
		}
		return DomainType.UNKNOWN;
	}
	
	public boolean isCanonical(){
		return false;
	}
/*	
	public Object getMin()
	{
		Object o=null;
		switch(domaintype)
		{
		case INTEGER:
			IntegerDomain inter=(IntegerDomain)this;
			if (inter.getIntervals().size() > 0) {
				return inter.getIntervals().first().getMin();
			}else{
				return Long.MAX_VALUE;
			}
		case DOUBLE:
			DoubleDomain dou=(DoubleDomain)this;
			if (dou.getIntervals().size() > 0) {
				return dou.getIntervals().first().getMin();
			}else{
				return Double.POSITIVE_INFINITY;
			}
		default:
				
		}
		return o;
	}
	
	public Object getMax()
	{
		Object o=null;
		switch(domaintype)
		{
		case INTEGER:
			IntegerDomain inter=(IntegerDomain)this;
			if (inter.getIntervals().size() > 0) {
				return inter.getIntervals().last().getMax();
			}else{
				return Long.MIN_VALUE;
			}
		case DOUBLE:
			DoubleDomain dou=(DoubleDomain)this;
			if (dou.getIntervals().size() > 0) {
				return dou.getIntervals().last().getMax();
			}else{
				return Double.NEGATIVE_INFINITY;
			}
		default:
				
		}
		return o;
	}
*/	
	public static Domain wideningDomain(Domain before,Domain after)
	{
			if(before==null){
				return after;
			}else if(after==null){
				return before;
			}
			if(before.equals(after))
				return before;
					
		Domain retDomain=null;
		DomainType dt=before.getDomaintype();
		
		switch(dt){
		case INTEGER:
			if(before.unknown || after.unknown)
				return  IntegerDomain.getUnknownDomain();
			long d_min,d_max,a_min,a_max,b_min,b_max;
			a_min=((IntegerDomain)before).getMin();
			a_max=((IntegerDomain)before).getMax();
			after=Domain.castToType(after, CType_BaseType.intType);
			b_min=((IntegerDomain)after).getMin();
			b_max=((IntegerDomain)after).getMax();
			
			if(b_min<a_min){
				d_min=Long.MIN_VALUE;
			}else{
				d_min=a_min;
			}
			
			if(b_max>a_max){
				d_max=Long.MAX_VALUE;
			}else{
				d_max=a_max;
			}
			IntegerInterval t=new IntegerInterval(d_min,d_max);
			retDomain=new IntegerDomain(t);
			break;
		case DOUBLE:
			if(before.unknown || after.unknown)
				return  DoubleDomain.getUnknownDomain();
			double r_min,r_max,x_min,x_max,y_min,y_max;
			x_min=((DoubleDomain)before).getMin();
			x_max=((DoubleDomain)before).getMax();
			after=Domain.castToType(after, CType_BaseType.doubleType);
			y_min=((DoubleDomain)after).getMin();
			y_max=((DoubleDomain)after).getMax();
			
			if(y_min<x_min){
				r_min=Long.MIN_VALUE;
			}else{
				r_min=x_min;
			}
			
			if(y_max>x_max){
				r_max=Long.MAX_VALUE;
			}else{
				r_max=x_max;
			}
			DoubleInterval d=new DoubleInterval(r_min,r_max);
			retDomain=new DoubleDomain(d);
			break;
		case POINTER:
			if(before.unknown || after.unknown)
				return  IntegerDomain.getUnknownDomain();
			retDomain=new PointerDomain();
			
			PointerDomain beforePointDomain;
			
			beforePointDomain=(PointerDomain)Domain.union(Domain.castToPointerDomain(before), Domain.castToPointerDomain(after), new CType_Pointer());
			retDomain=beforePointDomain;
//			IntegerDomain allocRange=null;
//			CType_AllocType allocType=null;
			CType elementType=beforePointDomain.getElementtype();			
			((PointerDomain)retDomain).setElementtype(elementType);
//			Expression length=null;
//			String name=null;
//			IntegerDomain offsetRange=null;
//			Domain realDomain=null;
//			PointerValue value=null;
			
			//dongyk 20120611 如果是ArrayDomain，转化为PointDomain
			
			break;
		case UNKNOWN:
			break;
		default:
				break;
		}
		
		return retDomain;
	}
	
	public static Domain narrowingDomain(Domain before,Domain after)
	{
		
			if(before==null){
				return after;
			}else if(after==null){
				return before;
			}
			if(before.equals(after))
				return before;
		
		Domain retDomain=null;
		DomainType dt=before.getDomaintype();
		
		switch(dt){
		case INTEGER:
			if(before.unknown || after.unknown)
				return  IntegerDomain.getUnknownDomain();
			long d_min,d_max,a_min,a_max,b_min,b_max;
			a_min=((IntegerDomain)before).getMin();
			a_max=((IntegerDomain)before).getMax();
			after=Domain.castToType(after, CType_BaseType.intType);
			b_min=((IntegerDomain)after).getMin();
			b_max=((IntegerDomain)after).getMax();
			
			if(a_min==Long.MIN_VALUE){
				d_min=b_min;
			}else{
				d_min=Math.min(a_min, b_min);
			}
			
			if(a_max==Long.MAX_VALUE){
				d_max=b_max;
			}else{
				d_max=Math.max(a_max, b_max);
			}
			IntegerInterval t=new IntegerInterval(d_min,d_max);
			retDomain=new IntegerDomain(t);
			break;
		case DOUBLE:
			if(before.unknown || after.unknown)
				return  DoubleDomain.getUnknownDomain();
			double r_min,r_max,x_min,x_max,y_min,y_max;
			x_min=((DoubleDomain)before).getMin();
			x_max=((DoubleDomain)before).getMax();
			after=Domain.castToType(after, CType_BaseType.doubleType);
			y_min=((DoubleDomain)after).getMin();
			y_max=((DoubleDomain)after).getMax();
			
			if(x_min==Long.MIN_VALUE){
				r_min=y_min;
			}else{
				r_min=Math.min(x_min, y_min);
			}
			
			if(x_max==Long.MAX_VALUE){
				r_max=y_max;
			}else{
				r_max=Math.max(x_max, y_max);
			}
			DoubleInterval d=new DoubleInterval(r_min,r_max);
			retDomain=new DoubleDomain(d);
			break;
		case POINTER:
			if(before.unknown || after.unknown)
				return  IntegerDomain.getUnknownDomain();
			retDomain=new PointerDomain();
			
//			IntegerDomain allocRange=null;
//			CType_AllocType allocType=null;
			CType elementType=((PointerDomain)before).getElementtype();
			((PointerDomain)retDomain).setElementtype(elementType);
//			Expression length=null;
//			String name=null;
//			IntegerDomain offsetRange=null;
//			Domain realDomain=null;
//			PointerValue value=null;
			break;
		case UNKNOWN:
			break;
		default:
				break;
		}
		
		return retDomain;
	}
	/**
	 * 获得指定类型区间的unknown区间
	 * 
	 * @param type
	 *            指定区间类型
	 * @return 返回指定区间类型的unknown区间
	 */
	public static Domain getUnknownDomain(DomainType type) {
		Domain ret = null;
		switch (type) {
		
		case POINTER:
			ret = PointerDomain.getUnknownDomain();
			break;
		case INTEGER:
			ret = IntegerDomain.getUnknownDomain();
			break;
		case DOUBLE:
			ret = DoubleDomain.getUnknownDomain();
			break;
		
		}
		return ret;
	}
}