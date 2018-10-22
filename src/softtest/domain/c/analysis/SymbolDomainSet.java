package softtest.domain.c.analysis;

import java.util.*;

import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.Type.CType;
import softtest.symboltable.c.Type.CType_BaseType;
import softtest.symboltable.c.Type.CType_Pointer;

/** 域集 */
public class SymbolDomainSet {
	/** 从符号到域的哈希表 */
	private Hashtable<SymbolFactor, Domain> domaintable = new Hashtable<SymbolFactor, Domain>();

	/** 缺省构造函数 */
	public SymbolDomainSet() {

	}

	/** 拷贝构造函数 ,当前并没有进行深层拷贝*/
	public SymbolDomainSet(SymbolDomainSet ds) {
		Domain domain = null;
		Hashtable<SymbolFactor, Domain> table=ds.domaintable;
		for(SymbolFactor v : table.keySet())
		{
			domain=table.get(v);
			addDomain(v, domain);
		}
	}

	/** 设置符号v的域 */
	public Domain addDomain(SymbolFactor v, Domain domain) {
		return domaintable.put(v, domain);
	}

	/** 获得符号v的域 */
	public Domain getDomain(SymbolFactor v) {
		return domaintable.get(v);
	}

	/** 清除哈希表 */
	public void clearDomainSet() {
		domaintable.clear();
	}

	/** 设置哈希表 */
	public void setTable(Hashtable<SymbolFactor, Domain> domaintable) {
		this.domaintable = domaintable;
	}

	/** 获得哈希表 */
	public Hashtable<SymbolFactor, Domain> getTable() {
		return domaintable;
	}

	/** 判断哈希表是否为空 */
	public boolean isEmpty() {
		return domaintable.isEmpty();
	}

	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		
		if (domaintable.size() == 0) {
			b.append("empty");
			return b.toString();
		}
		
		Domain domain=null;
		for(SymbolFactor v : domaintable.keySet())
		{
			domain=domaintable.get(v);
			b.append(v.getSymbol() + ":" + domain + "  ");
		}
		
		return b.toString();
	}
	
	
	/** 判断域集是否存在矛盾，如果有任何一个符号的域为空则认为是矛盾 */
	public boolean isContradict() {
		for(Domain d : domaintable.values()) {
			switch (d.getDomaintype()) {
			case INTEGER:
				if (((IntegerDomain) d).isEmpty()) {
					return true;
				}
				break;
			case DOUBLE:
				if (((DoubleDomain) d).isEmpty()) {
					return true;
				}
				break;
			case POINTER:
				if (((PointerDomain) d).getValue() == PointerValue.EMPTY) {
					return true;
				}
				break;
			}
		}
		return false;
	}
	
	public static SymbolDomainSet union(SymbolDomainSet a,SymbolDomainSet b){
		SymbolDomainSet r = new SymbolDomainSet();
		if(a==null && b==null)
			return null;
		
		if (a == null) {
			a = new SymbolDomainSet();
		}
		if (b == null) {
			b = new SymbolDomainSet();
		}
		
		Domain d1 = null, d2 = null;
		
		Hashtable<SymbolFactor, Domain> table=a.domaintable;
		for(SymbolFactor v1 : table.keySet())
		{
			d1=table.get(v1);
			d2=b.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				r.addDomain(v1, d1);
			} else {
				r.addDomain(v1,Domain.union(d1, d2, type));
			}
		}

		// 将b的那些a没有出现的插入到table中
		table = b.domaintable;
		for(SymbolFactor v2 : table.keySet())
		{
			d2 = table.get(v2);
			// 在domainset中查找
			d1 = a.getDomain(v2);
			if (d1 == null) {
				r.addDomain(v2, d2);
			}
		}
		return r;
	}
	
	public static SymbolDomainSet intersect(SymbolDomainSet a, SymbolDomainSet b) {
		SymbolDomainSet r = new SymbolDomainSet();
		if(a==null && b==null)
			return null;
		
		if (a == null) {
			a = new SymbolDomainSet();
		}
		if (b == null) {
			b = new SymbolDomainSet();
		}
		
		Domain d1 = null, d2 = null;
		
		Hashtable<SymbolFactor, Domain> table=a.domaintable;
		for(SymbolFactor v1 : table.keySet())
		{
			d1=table.get(v1);
			d2=b.getDomain(v1);
			CType type=v1.getType();
			if (d2 == null) {
				r.addDomain(v1, d1);
			} else {
				r.addDomain(v1,Domain.intersect(d1, d2, type));
			}
		}

		// 将b的那些a没有出现的插入到table中
		table = b.domaintable;
		for(SymbolFactor v2 : table.keySet())
		{
			d2 = table.get(v2);
			// 在domainset中查找
			d1 = a.getDomain(v2);
			if (d1 == null) {
				r.addDomain(v2, d2);
			}
		}
		return r;
	}
	
	public boolean contains(SymbolDomainSet ss)
	{
		Hashtable<SymbolFactor, Domain> table=domaintable;
		for(SymbolFactor v : table.keySet())
		{
			Domain domain=table.get(v);
			Domain ssDomain=ss.getDomain(v);			
			if(domain!=null&&ssDomain!=null)
			{
				DoubleDomain d1=Domain.castToDoubleDomain(domain);
				DoubleDomain d2=Domain.castToDoubleDomain(ssDomain);
				if(!d1.contains(d2))
				{
					return false;
				}
			}
		}		
		return true;
	}
}
