package softtest.domain.c.analysis;

import java.util.*;

import softtest.ast.c.Node;
import softtest.cfg.c.*;
import softtest.config.c.Config;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_AllocType;
import softtest.symboltable.c.Type.CType_Pointer;


/** 条件限定域集 */
public class ConditionData {

	/** 条件限定域 */
	class ConditionDomains {
		/** 可能域 */
		Domain may;

		/** 肯定域 */
		Domain must;
	}
	public ConditionData (VexNode currentvex){
		this.currentvex=currentvex;
	}
	
//	/**拷贝构造函数 */
//	public ConditionData(ConditionData oldcondata) {
//		this.currentvex=oldcondata.currentvex;
//		Hashtable<SymbolFactor, ConditionDomains> oldtable=oldcondata.getDomainsTable();
//		for(SymbolFactor s : oldtable.keySet())
//		{
//			ConditionDomains condoms=oldtable.get(s);
//			domainstable.put(s, condoms);
//		}
//	}

	VexNode currentvex=null;
	
	public VexNode getCurrentVex(){
		return currentvex;
	}
	
	public void setCurrentVex(VexNode currentvex){
		this.currentvex=currentvex;
	}

	/** 从变量到条件限定域的哈希表 */
	private Hashtable<SymbolFactor, ConditionDomains> domainstable = new Hashtable<SymbolFactor, ConditionDomains>();

	/** 设置哈希表 */
	public void setDomainsTable(Hashtable<SymbolFactor, ConditionDomains> domainstable) {
		this.domainstable = domainstable;
	}

	/** 获得哈希表 */
	public Hashtable<SymbolFactor, ConditionDomains> getDomainsTable() {
		return domainstable;
	}
	
	/** 判断指定变量是否在当前条件限定域集中 */
	public boolean isSymbolContained(SymbolFactor s){
		return domainstable.containsKey(s);
	}

	/** 设置符号s的可能域 */
	public void addMayDomain(SymbolFactor s, Domain domain) {
		ConditionDomains domains = null;
		if (domainstable.containsKey(s)) {
			domains = domainstable.get(s);
		} else {
			domains = new ConditionDomains();
			domainstable.put(s, domains);
		}
		//当v为无符号类型时，将其区间域的负数部分舍去
		//modified by zhouhb
		//2011.10.25
		if(s.getType().getName().contains("unsigned")){
			//dongyk 20120614
			if(domain instanceof PointerDomain)
			{
				domain=PointerDomain.castToIntegerDomain(domain);
			}
			domain=IntegerDomain.intersect(new IntegerDomain(0,IntegerDomain.DEFAULT_MAX), (IntegerDomain)domain);
			domains.may = domain;
		}else{
			domains.may = domain;
		}
	}

	/** 设置符号s的肯定域 */
	public void addMustDomain(SymbolFactor s, Domain domain) {
		ConditionDomains domains = null;
		if (domainstable.containsKey(s)) {
			domains = domainstable.get(s);
		} else {
			domains = new ConditionDomains();
			domainstable.put(s, domains);
		}
		//当v为无符号类型时，将其区间域的负数部分舍去
		//modified by zhouhb
		//2011.10.25
		if(s.getType().getName().contains("unsigned")){
			//dongyk 20120614
			if(domain instanceof PointerDomain)
			{
				domain=PointerDomain.castToIntegerDomain(domain);
			}
			domain=IntegerDomain.intersect(new IntegerDomain(0,IntegerDomain.DEFAULT_MAX), (IntegerDomain)domain);
			domains.must = domain;
		}else{
			domains.must = domain;
		}
	}

	/** 获得符号s的可能域 */
	public Domain getMayDomain(SymbolFactor s) {
		if(s==null)
			return null;
		ConditionDomains domains = domainstable.get(s);
		if (domains == null) {
			return null;
		}
		return domains.may;
	}

	/** 获得符号s的肯定域 */
	public Domain getMustDomain(SymbolFactor s) {
		ConditionDomains domains = domainstable.get(s);
		if (domains == null) {
			return null;
		}
		return domains.must;
	}

	/** 清除哈希表 */
	public void clearDomains() {
		domainstable.clear();
	}

	/** 获得条件为真前提下的条件限定可能域集 */
	public SymbolDomainSet getTrueMayDomainSet() {
		SymbolDomainSet ret= new SymbolDomainSet();
		Set<Map.Entry<SymbolFactor, ConditionDomains>> entry = domainstable.entrySet();
		Iterator<Map.Entry<SymbolFactor, ConditionDomains>> i = entry.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor, ConditionDomains> e = i.next();
			if (e.getValue().may != null) {
				ret.addDomain(e.getKey(), e.getValue().may);
			}
		}
		return ret;
	}

	/** 获得条件为假前提下的条件限定可能域集 */
	public SymbolDomainSet getFalseMayDomainSet() {
		SymbolDomainSet ret= new SymbolDomainSet();
		Set<Map.Entry<SymbolFactor, ConditionDomains>> entry = domainstable.entrySet();
		Iterator<Map.Entry<SymbolFactor, ConditionDomains>> i = entry.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor, ConditionDomains> e = i.next();
			SymbolFactor s=e.getKey();
			if (e.getValue().must != null) {
				Domain a=s.getDomainWithoutNull(currentvex.getSymDomainset());
				CType type=s.getType();
				Domain b = e.getValue().must;
				Domain result=Domain.substract(a, b, type);
				if(result instanceof PointerDomain){
					if(((PointerDomain)result).getValue().toString().equals("NOTNULL")&&((PointerDomain)result).Type.isEmpty())
						((PointerDomain)result).Type.add(CType_AllocType.NotNull);
					else if(((PointerDomain)result).getValue().toString().equals("NULL")&&((PointerDomain)result).Type.isEmpty())
						((PointerDomain)result).Type.add(CType_AllocType.Null);
				}
				//对指针变量进行判断
				//add by zhouhb 2010/7/19
				if(a instanceof PointerDomain && result instanceof PointerDomain &&((PointerDomain)result).allocRange.isEmpty()){
					((PointerDomain)result).allocRange=new IntegerDomain(0,0);
				}
				ret.addDomain(s, result);
			}
		}
		return ret;
	}

	/** 获得条件为真前提下的条件限定肯定域集 */
	public SymbolDomainSet getTrueMustDomainSet() {
		SymbolDomainSet ret= new SymbolDomainSet();
		Set<Map.Entry<SymbolFactor, ConditionDomains>> entry = domainstable.entrySet();
		Iterator<Map.Entry<SymbolFactor, ConditionDomains>> i = entry.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor, ConditionDomains> e = i.next();
			if (e.getValue().must != null) {
				ret.addDomain(e.getKey(), e.getValue().must);
			}
		}
		return ret;
	}

	/** 获得条件为假前提下的条件限定肯定域集 */
	public SymbolDomainSet getFalseMustDomainSet() {
		SymbolDomainSet ret= new SymbolDomainSet();
		Set<Map.Entry<SymbolFactor, ConditionDomains>> entry = domainstable.entrySet();
		Iterator<Map.Entry<SymbolFactor, ConditionDomains>> i = entry.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor, ConditionDomains> e = i.next();
			SymbolFactor s=e.getKey();
			if (e.getValue().may != null) {
				Domain a=s.getDomainWithoutNull(currentvex.getSymDomainset());
				CType type=s.getType();
				Domain b = e.getValue().may;
				Domain result=Domain.substract(a, b, type);
				if(result instanceof PointerDomain){
					if(((PointerDomain)result).getValue().toString().equals("NOTNULL")&&((PointerDomain)result).Type.isEmpty())
						((PointerDomain)result).Type.add(CType_AllocType.NotNull);
					else if(((PointerDomain)result).getValue().toString().equals("NULL")&&((PointerDomain)result).Type.isEmpty())
						((PointerDomain)result).Type.add(CType_AllocType.Null);
				}
				//对指针变量进行判断
				//add by zhouhb 2010/7/19
				if(a instanceof PointerDomain){					
					if(result instanceof IntegerDomain)
					{
						result=Domain.castToType(result, new CType_Pointer());
					}
					if(result instanceof PointerDomain&&((PointerDomain)result).allocRange.isEmpty())
					{
						((PointerDomain)result).allocRange=new IntegerDomain(0,0);
					}
				}
				ret.addDomain(s, result);
			}
		}
		return ret;
	}

	/** 判断条件限定可能域是否矛盾 */
	public boolean isMayContradict() {
		SymbolDomainSet ds=getTrueMayDomainSet();
		return ds.isContradict();
	}

	/** 判断条件限定肯定域是否矛盾 */
	public boolean isMustContradict() {
		SymbolDomainSet ds=getTrueMustDomainSet();
		return ds.isContradict();
	}
	
	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		Set<Map.Entry<SymbolFactor, ConditionDomains>> entryset = domainstable.entrySet();
		Iterator<Map.Entry<SymbolFactor, ConditionDomains>> i = entryset.iterator();
		SymbolFactor v = null;
		ConditionDomains d = null;
		while (i.hasNext()) {
			Map.Entry<SymbolFactor, ConditionDomains> e = i.next();
			v = e.getKey();
			d = e.getValue();
			b.append("" + v.getSymbol() + ":{may:" + d.may + "must:" + d.must + "}");
		}
		return b.toString();
	}
	
	private boolean isLogicallyTrueBut(SymbolDomainSet ds,SymbolFactor v){
		SymbolFactor v1 = null;
		Domain d1 = null,d2=null;
		Set<Map.Entry<SymbolFactor,Domain>> entryset = ds.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 = e.getKey();
			d1= e.getValue();
			if(v1==v){
				continue;
			}
			d2=v1.getDomainWithoutNull(currentvex.getSymDomainset());
			if(d2.equals(d1)){
				return true;
			}
		}		
		return false;
	}
	
	private boolean isContradicBut(SymbolDomainSet ds,SymbolFactor v){
		SymbolFactor v1 = null;
		Domain d1 = null;
		Set<Map.Entry<SymbolFactor,Domain>> entryset = ds.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 = e.getKey();
			d1=e.getValue();
			if(v1==v){
				continue;
			}
			if(Domain.isEmpty(d1)){
				return true;
			}
		}
		return false;
	}
	
	/** 将域集中的所有域设置为相应的条件限定肯定域 */
	public void addMustDomain(SymbolDomainSet ds) {
		Set<Map.Entry<SymbolFactor,Domain>> entryset = ds.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		SymbolFactor v = null;
		Domain d = null;
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e =  i.next();
			v = (SymbolFactor) e.getKey();
			d = e.getValue();
			addMustDomain(v, d);
		}
	}

	/** 将域集中的所有域设置为相应的条件限定可能域 */
	public void addMayDomain(SymbolDomainSet ds) {
		Set<Map.Entry<SymbolFactor,Domain>> entryset = ds.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		SymbolFactor v = null;
		Domain d = null;
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e =  i.next();
			v = (SymbolFactor) e.getKey();
			d = e.getValue();
			addMayDomain(v, d);
		}
	}
	
	public ConditionData calLogicalAndExpression(ConditionData leftdata,ConditionData rightdata){
		ConditionData r=new ConditionData(currentvex);
		SymbolDomainSet may1 = leftdata.getTrueMayDomainSet();
		SymbolDomainSet may2 = rightdata.getTrueMayDomainSet();

		SymbolDomainSet must1 = leftdata.getTrueMustDomainSet();
		SymbolDomainSet must2 = rightdata.getTrueMustDomainSet();
		
		SymbolDomainSet may=new SymbolDomainSet();
		SymbolDomainSet must=new SymbolDomainSet();
		
		SymbolFactor v1 = null, v2 = null;
		Domain d1 = null, d2 = null;
		Set<Map.Entry<SymbolFactor,Domain>> entryset = may1.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 = (SymbolFactor) e.getKey();
			d1 = e.getValue();
			// 在domainset中查找
			d2 = may2.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				if(!isContradicBut(may2,v1)){
					Domain d=v1.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v1,Domain.intersect(d, d1, type));
				}else{
					//always FALSE, add EMPTY
					may.addDomain(v1,Domain.getEmptyDomainFromType(type));
				}
			} else {
				// 取intersect
				may.addDomain(v1, Domain.intersect(d1, d2,v1.getType()));
			}
		}

		// 将b的那些a没有出现的插入到table中
		entryset = may2.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e =  i.next();
			v2 = e.getKey();
			d2 = e.getValue();
			// 在domainset中查找
			d1 = may1.getDomain(v2);
			CType type=v2.getType();
			if (d1 == null) {
				if(!isContradicBut(may1,v2)){
					Domain d=v2.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v2,Domain.intersect(d, d2, type));
				}else{
					//always FALSE, add EMPTY
					may.addDomain(v2,Domain.getEmptyDomainFromType(type));
				}				
			}
		}		
		
		r.addMayDomain(may);
		//计算must
		entryset = must1.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 = (SymbolFactor) e.getKey();
			d1 = e.getValue();
			// 在domainset中查找
			d2 = must2.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				if(isLogicallyTrueBut(must2,v1)){
					//永真，取当前取左操作数的must
					must.addDomain(v1, d1);
				}else{
					must.addDomain(v1,Domain.getEmptyDomainFromType(type));
				}
			} else {
				// 取intersect
				must.addDomain(v1,Domain.intersect(d1, d2,v1.getType()));
			}
		}

		// 将b的那些a没有出现的插入到table中
		entryset = must2.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v2 = e.getKey();
			d2 = e.getValue();
			// 在domainset中查找
			d1 = must1.getDomain(v2);
			if (d1 == null) {
				if(isLogicallyTrueBut(must1,v2)){
					//永真，取左操作数的must
					must.addDomain(v2, d2);
				}else{				
					must.addDomain(v2, Domain.getEmptyDomainFromType(v2.getType()));
				}			
			}else{
				must.addDomain(v2,Domain.intersect(d1, d2,v2.getType()));
			}
		}		
		
		r.addMustDomain(must);			
		return r;
	}
	
	public ConditionData calLogicalOrExpression(ConditionData leftdata,ConditionData rightdata){
		ConditionData r=new ConditionData(currentvex);
		SymbolDomainSet may1 = leftdata.getTrueMayDomainSet();
		SymbolDomainSet may2 = rightdata.getTrueMayDomainSet();

		SymbolDomainSet must1 = leftdata.getTrueMustDomainSet();
		SymbolDomainSet must2 = rightdata.getTrueMustDomainSet();
		
		SymbolDomainSet may=new SymbolDomainSet();
		SymbolDomainSet must=new SymbolDomainSet();
		
		SymbolFactor v1 = null, v2 = null;
		Domain d1 = null, d2 = null;
		Set<Map.Entry<SymbolFactor,Domain>> entryset = may1.getTable().entrySet();
		Iterator<Map.Entry<SymbolFactor,Domain>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 =  e.getKey();
			d1 = e.getValue();
			// 在domainset中查找
			d2 = may2.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				if(!isContradicBut(may2,v1)){
					//不矛盾，取全集
					Domain d=v1.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v1,Domain.intersect(d, Domain.getFullDomainFromType(type), type));
				}else{
					//矛盾，取左操作数的may
					may.addDomain(v1, d1);
				}
			} else {
				// 取union，
				may.addDomain(v1, Domain.union(d1, d2,v1.getType()));
			}
		}

		// 将b的那些a没有出现的插入到table中
		entryset = may2.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e =  i.next();
			v2 =  e.getKey();
			d2 = e.getValue();
			// 在domainset中查找
			d1 = may1.getDomain(v2);
			CType type=v2.getType();
			if (d1 == null) {
				if(!isContradicBut(may1,v2)){
					//不矛盾，取全集
					Domain d=v2.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v2,Domain.intersect(d, Domain.getFullDomainFromType(type), type));
				}else{
					//矛盾，取左操作数的may
					may.addDomain(v2, d2);
				}
			}
		}		
		
		r.addMayDomain(may);
		//计算must
		entryset = must1.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain> e = i.next();
			v1 = e.getKey();
			d1 = e.getValue();
			// 在domainset中查找
			d2 = must2.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				if (isLogicallyTrueBut(must2, v1)) {
					// 永真，取全集
					Domain d=v1.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v1,Domain.intersect(d, Domain.getFullDomainFromType(type), type));
				}else{
					//不永真，取左操作数的must
					must.addDomain(v1, d1);
				}
			} else {
				// 取union，数组特殊处理
				must.addDomain(v1, Domain.union(d1, d2,v1.getType()));
			}
		}

		// 将b的那些a没有出现的插入到table中
		entryset = must2.getTable().entrySet();
		i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<SymbolFactor,Domain>e =  i.next();
			v2 =  e.getKey();
			d2 = e.getValue();
			// 在domainset中查找
			d1 = must1.getDomain(v2);
			CType type=v2.getType();
			if (d1 == null) {
				if(isLogicallyTrueBut(must1,v2)){
					//永真，取全集	
					Domain d=v2.getDomainWithoutNull(currentvex.getSymDomainset());
					may.addDomain(v2,Domain.intersect(d, Domain.getFullDomainFromType(type), type));
				}else{
					//不永真，取左操作数的must
					must.addDomain(v2, d2);
				}
			}
		}		
		
		r.addMustDomain(must);		
		return r;
	}
	
	public static ConditionData calLoopCondtion(ConditionData data,VexNode vex,ConditionDomainVisitor convisitor,Node treenode){
		treenode.jjtAccept(convisitor, data);
		if(!Config.LOOPCAL || DomainVexVisitor.looplayer > Config.LOOPLAYER){
			//zys:2010.11.11	如果没有对循环进行正确处理,则需要生成正确的MUST区间；
			//这种处理是CPP中只对循环处理一次的做法，虽然出口区间保守，但循环内的区间是错误的
			SymbolDomainSet old=vex.getSymDomainset();
			ConditionData data1=new ConditionData(vex);
			vex.setSymDomainset(null);
			treenode.jjtAccept(convisitor, data1);
			vex.setSymDomainset(old);
			
			Set entryset = data1.domainstable.entrySet();
			Iterator i = entryset.iterator();
			while (i.hasNext()) {
				Map.Entry e = (Map.Entry) i.next();
				SymbolFactor v = (SymbolFactor) e.getKey();
				ConditionDomains d = (ConditionDomains)e.getValue();
				data.addMustDomain(v, d.must);
			}
		}
		return data;
	}
}
