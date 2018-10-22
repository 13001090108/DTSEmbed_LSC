package softtest.domain.c.analysis;

import java.util.*;
import java.util.Map.Entry;

import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.VariableNameDeclaration;


/** 域集 */
public class VarDomainSet {
	/** 从变量到域的哈希表 */
	private Hashtable<VariableNameDeclaration, Domain> domaintable = new Hashtable<VariableNameDeclaration, Domain>();

	public boolean equals(Object o) {
		if(!(o instanceof VarDomainSet))
			return false;
		if(o==null)
			return false;
		Hashtable<VariableNameDeclaration, Domain> othertable=((VarDomainSet)o).getTable();
		if(othertable.size()!=domaintable.size())
			return false;
		Domain otherdomain=null;
		Domain thisdomain=null;
		for(VariableNameDeclaration v : domaintable.keySet()){
			otherdomain=othertable.get(v);
			if(otherdomain==null){
				return false;
			}else{
				thisdomain=domaintable.get(v);
				if(!otherdomain.equals(thisdomain))
					return false;
			}
		}
		return true;
	}
	
	/** 缺省构造函数 */
	public VarDomainSet() {

	}

	/** 拷贝构造函数 ,当前并没有进行深层拷贝*/
	public VarDomainSet(VarDomainSet ds) {
		VariableNameDeclaration v = null;
		Domain domain = null;
		Set entryset = ds.domaintable.entrySet();
		Iterator i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry e = (Map.Entry) i.next();
			v = (VariableNameDeclaration) e.getKey();
			domain = (Domain)e.getValue();
			addDomain(v, domain);
		}
	}

	/** 设置v的域 */
	public Domain addDomain(VariableNameDeclaration v, Domain domain) {
		return domaintable.put(v, domain);
	}

	/** 获得v的域 */
	public Domain getDomain(VariableNameDeclaration v) {
		return domaintable.get(v);
	}

	/** 清除哈希表 */
	public void clearDomainSet() {
		domaintable.clear();
	}

	/** 设置哈希表 */
	public void setTable(Hashtable<VariableNameDeclaration, Domain> domaintable) {
		this.domaintable = domaintable;
	}

	/** 获得哈希表 */
	public Hashtable<VariableNameDeclaration, Domain> getTable() {
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
		Set entryset = domaintable.entrySet();
		Iterator i = entryset.iterator();
		VariableNameDeclaration v = null;
		Domain d = null;
		while (i.hasNext()) {
			Map.Entry e = (Map.Entry) i.next();
			v = (VariableNameDeclaration) e.getKey();
			d = (Domain)e.getValue();
			b.append(v.getImage() + ":" + d + "  ");
		}
		if (entryset.size() == 0) {
			b.append("Unknown");
		}
		return b.toString();
	}
	
	
	/** 判断域集是否存在矛盾，如果有任何一个符号的域为空则认为是矛盾 */
	public boolean isContradict() {
		Domain d = null;
		Set entryset = domaintable.entrySet();
		Iterator i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry e = (Map.Entry) i.next();
			d = (Domain)e.getValue();
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
	
	public static VarDomainSet union(VarDomainSet a,VarDomainSet b)
	{
		VarDomainSet r=new VarDomainSet();
		if(a==null){
			a=new VarDomainSet();
		}
		if(b==null){
			b=new VarDomainSet();
		}
		Domain d1=null,d2=null;
		
		//取将a、 b中相同的变量，对其区间执行并操作
		for(VariableNameDeclaration v : a.domaintable.keySet())
		{
			d1=a.getDomain(v);
			d2=b.getDomain(v);
			if(d2!=null)
			{
				r.addDomain(v, Domain.union(d1, d2, v.getType()));
			}
		}
		
		//将在b中出现，但没在a中出现的变量，加入r
		for(VariableNameDeclaration v : b.domaintable.keySet())
		{
			d2=b.getDomain(v);
			if(a.getDomain(v)==null)
			{
				r.addDomain(v, d2);
			}
		}
		return r;
	}
	
	
	public static VarDomainSet widening(VarDomainSet pre,VarDomainSet post,VexNode loopHead)
	{
		VarDomainSet r=new VarDomainSet();
		if(pre==null){
			pre=new VarDomainSet();
		}
		if(post==null){
			post=new VarDomainSet();
		}
		Domain d1=null,d2=null;
		
		//取将a、 b中相同的变量，对其区间执行并操作
		for(VariableNameDeclaration v : pre.domaintable.keySet())
		{
			d1=pre.getDomain(v);
			d2=post.getDomain(v);
			if(d2!=null)
			{
				r.addDomain(v, Domain.wideningDomain(d1, d2));
			}
		}
		
		//将在b中出现，但没在a中出现的变量，加入r
		for(VariableNameDeclaration v : post.domaintable.keySet())
		{
			d2=post.getDomain(v);
			if(pre.getDomain(v)==null)
			{
				r.addDomain(v, d2);
			}
		}
		
		SymbolDomainSet sds=loopHead.getSymDomainset();
		ValueSet vs=loopHead.getValueSet();
		Iterator<Entry<VariableNameDeclaration, Domain>> it=r.domaintable.entrySet().iterator();
		while(it.hasNext())
		{
			Entry<VariableNameDeclaration, Domain> e=it.next();
			VariableNameDeclaration v=e.getKey();
			Domain d=e.getValue();
			
			SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
			Expression expr=new Expression(s);
			sds.addDomain(s, d);
			vs.addValue(v, expr);
		}
		return r;
	}
	
	public static VarDomainSet narrowing(VarDomainSet pre,VarDomainSet post,VexNode loopHead)
	{
		VarDomainSet r=new VarDomainSet();
		if(pre==null){
			pre=new VarDomainSet();
		}
		if(post==null){
			post=new VarDomainSet();
		}
		Domain d1=null,d2=null;
		
		//取将a、 b中相同的变量，对其区间执行并操作
		for(VariableNameDeclaration v : pre.domaintable.keySet())
		{
			d1=pre.getDomain(v);
			d2=post.getDomain(v);
			if(d2!=null)
			{
				Domain d=Domain.narrowingDomain(d1, d2);
				r.addDomain(v, d);
			}
		}
		
		//将在b中出现，但没在a中出现的变量，加入r
		for(VariableNameDeclaration v : post.domaintable.keySet())
		{
			d2=post.getDomain(v);
			if(pre.getDomain(v)==null)
			{
				r.addDomain(v, d2);
			}
		}
		
		SymbolDomainSet sds=loopHead.getSymDomainset();
		ValueSet vs=loopHead.getValueSet();
		Iterator<Entry<VariableNameDeclaration, Domain>> it=r.domaintable.entrySet().iterator();
		while(it.hasNext())
		{
			Entry<VariableNameDeclaration, Domain> e=it.next();
			VariableNameDeclaration v=e.getKey();
			Domain d=e.getValue();
			
			SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
			Expression expr=new Expression(s);
			sds.addDomain(s, d);
			vs.addValue(v, expr);
		}
		return r;
	}
}
