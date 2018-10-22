package softtest.domain.c.interval;

import java.util.*;

import softtest.config.c.Config;

import softtest.symboltable.c.Type.CType_BaseType;

/** 整数域 */
public class IntegerDomain extends Domain {
	/** 区间集合，从小到大保持顺序的 */
	public TreeSet<IntegerInterval> intervals = new TreeSet<IntegerInterval>();
	public static long DEFAULT_MIN=Long.MIN_VALUE,DEFAULT_MAX=Long.MAX_VALUE;
	@Override
	public IntegerDomain clone() throws CloneNotSupportedException {
		IntegerDomain domain=(IntegerDomain)super.clone();
		domain.intervals=new TreeSet<IntegerInterval>();
		for(IntegerInterval i:intervals){
			domain.intervals.add((IntegerInterval)i.clone());
		}
		return domain;
	}
	
	/** 缺省构造函数 */
	public IntegerDomain() {
		domaintype=DomainType.INTEGER;
	}
		
	/** 得到一个全域*/
	public static IntegerDomain getFullDomain(){
		IntegerDomain r=new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE);
		return r;
	}
	
	/**
	 * 针对keil当中的数据类型溢出模式DOF，根据提供的类型type给出该类型的区间信息
	 * @param type
	 * @return type类型所对应的最大取值区间
	 * @author zys
	 */
	public static IntegerDomain getFullDomain(CType_BaseType type){
		IntegerDomain r=null;
		if(type.getName().equals(CType_BaseType.charType.toString()))
		{
			r=new IntegerDomain(-128,127);
		}else if(type.getName().equals(CType_BaseType.uCharType.toString()))
		{
			r=new IntegerDomain(0,255);
		}else if(type.getName().equals(CType_BaseType.shortType.toString()))
		{
			r=new IntegerDomain(-32768,32767);
		}else if(type.getName().equals(CType_BaseType.uShortType.toString()))
		{
			r=new IntegerDomain(0,65535);
		}else if(type.getName().equals(CType_BaseType.intType.toString()))
		{
			r=new IntegerDomain(-32768,32767);
		}else if(type.getName().equals(CType_BaseType.uIntType.toString()))
		{
			r=new IntegerDomain(0,65535);
		}else if(type.getName().equals(CType_BaseType.sfrType.toString()))
		{
			//zys:2010.4.22 PHILIPS 80C51MX提供一个附加扩展的SFR空间，地址范围是0x180到0x1FF
			r=new IntegerDomain(0,511);
		}else if(type.getName().equals(CType_BaseType.sfr16Type.toString()))
		{
			r=new IntegerDomain(0,65535);
		}
		return r;
	}
	
	/** 得到一个空域*/
	public static IntegerDomain getEmptyDomain(){
		IntegerDomain r=new IntegerDomain(Long.MAX_VALUE,Long.MIN_VALUE);
		return r;
	}
	
	/** 得到域中的区间集合*/
	public TreeSet<IntegerInterval> getIntervals(){
		return intervals;
	}

	/** 以指定的单一区间[min,max]构造域，minexcluded，maxexcluded指定min或max是否去除（为true的话即为开区间） */
	public IntegerDomain(long min, long max, boolean minexcluded, boolean maxexcluded) {
		this();
		IntegerInterval interval = new IntegerInterval(min, max, minexcluded, maxexcluded);
		if (!interval.isEmpty()) {
			intervals.add(interval);
		}
	}
	
	/** 以指定的单一区间[min,max]构造域*/
	public IntegerDomain(long min,long max){
		this(min,max,false,false);
	}

	/** 构造包含指定区间集合的域 */
	public IntegerDomain(IntegerInterval[] intervals) {
		this();
		for (int i = 0; i < intervals.length; i++) {
			this.mergeWith(intervals[i]);
		}
	}

	/** 构造只包含一个指定区间的域 */
	public IntegerDomain(IntegerInterval interval) {
		this();
		this.mergeWith(interval);
	}

	/** 拷贝构造函数 */
	public IntegerDomain(IntegerDomain domain) {
		this();
		for (IntegerInterval interval : domain.intervals) {
			if (!interval.isEmpty()) {
				this.intervals.add(new IntegerInterval(interval));
			}
		}
		this.setUnknown(domain.isUnknown());
	}
	
	/**
	 * 得到一个整型未知区间
	 * 
	 * @return 一个整未知区间
	 */
	public static IntegerDomain getUnknownDomain() {
		IntegerDomain r = new IntegerDomain();
		r.setUnknown(true);
		return r;
	}

	/** 判断域是否为空 */
	public boolean isEmpty() {
		IntegerDomain d = new IntegerDomain(this);
		if (d.unknown) {
			return false;
		}
		if (d.intervals.isEmpty()) {
			return true;
		} else {
			return false;
		}
	}
	
	/** 判断当前域是否包含数x*/
	public boolean contains(int x){
		if (unknown) {
			return true;
		}
		for (IntegerInterval interval : intervals) {
			if(interval.contains(x)){
				return true;
			}
		}
		return false;
	}
	
	/** 判断当前域是否包含域x*/
	public boolean contains(IntegerDomain x){
		if(x==null)
		{
			return false;
		}
		if (unknown) {
			return true;
		}
		if (x.unknown && !unknown) {
			return false;
		}
		IntegerDomain temp=IntegerDomain.union(this, x);
		if(temp.equals(this)){
			return true;
		}
		return false;
	}

	/** 判断域是否只包含一个数值 */
	@Override
	public boolean isCanonical() {
		if (unknown) {
			return false;
		}
		IntegerDomain d = new IntegerDomain(this);
		if (d.intervals.size() == 1) {
			for (IntegerInterval interval : d.intervals) {
				if (interval.isCanonical()) {
					return true;
				}
			}
		}
		return false;
	}

	/** 判断两个域是否相等，每个区间相等被认为两个域相等 */
	@Override
	public boolean equals(Object o) {
		if ((o == null) || !(o instanceof IntegerDomain)) {
			return false;
		}
		if (this == o) {
			return true;
		}
		IntegerDomain x = (IntegerDomain) o;
		
		if (this.unknown && x.unknown) {
			return true;
		}
		if(isEmpty()&&x.isEmpty()){
			return true;
		}

		IntegerDomain a = new IntegerDomain(this), b = new IntegerDomain(x);
		if (a.intervals.size() == b.intervals.size()) {
			Iterator<IntegerInterval> ia = a.intervals.iterator(), ib = b.intervals.iterator();
			while (ia.hasNext()) {
				IntegerInterval interval1 = ia.next(), interval2 = ib.next();
				if (!interval1.equals(interval2)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}
	
	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		if (unknown) {
			b.append("unknown");
		} else if (intervals.isEmpty()) {
			b.append("emptydomain");
		} else {
			boolean first = true;
			for (IntegerInterval interval : intervals) {
				if (first) {
					first = false;
				} else {
					b.append("U");
				}
				b.append(interval);
			}
		}
		return b.toString();
	}

	/** 获得一个包含域的最小区间，将域并为一个区间 */
	public IntegerInterval jointoOneInterval() {
		if (unknown) {
			return IntegerInterval.fullInterval();
		}
		long tmax = 0, tmin = 0;		
		if (intervals.size() > 0) {
			tmax = intervals.last().getMax();
			tmin = intervals.first().getMin();
		} else {
			tmax = Long.MIN_VALUE;
			tmin = Long.MAX_VALUE;
		}
		return new IntegerInterval(tmin, tmax);
	}
	
	public long getMin(){
		if (intervals.size() > 0) {
			return intervals.first().getMin();
		}else{
			return Long.MAX_VALUE;
		}
	}
	
	public long getMax(){
		if (intervals.size() > 0) {
			return intervals.last().getMax();
		}else{
			return Long.MIN_VALUE;
		}
	}


	/** 将新的区间和域合并，考虑合并时产生的区间融合 */
	public void mergeWith(IntegerInterval newInterval) {
		// 收集所有和新区间有重合的区间，并将其从集合中删除
		if (newInterval.isEmpty()) {
			return;
		}
		List<IntegerInterval> intersectors = new ArrayList<IntegerInterval>();
		List<IntegerInterval> toRemove = new ArrayList<IntegerInterval>();
		for (IntegerInterval interval : intervals) {
			if (interval.isEmpty() || IntegerInterval.canBeJoined(interval, newInterval)) {
				if (!interval.isEmpty()) {
					intersectors.add(interval);
				}
				toRemove.add(interval);
			}
		}
		intervals.removeAll(toRemove);

		// 将新区间和所有intersectors中的区间进行合并
		long min = newInterval.getMin();
		long max = newInterval.getMax();

		for (IntegerInterval intersector : intersectors) {
			if (intersector.getMin() < newInterval.getMin()) {
				min = intersector.getMin();
			}
			if (intersector.getMax() > newInterval.getMax()) {
				max = intersector.getMax();
			}
		}
		// 加入新区间
		intervals.add(new IntegerInterval(min, max));
	}

	/** 取两个区间的交集，返回一个新的区间 */
	private static IntegerInterval intersectionOf(IntegerInterval i1, IntegerInterval i2) {
		long new_min;
		long new_max;
		if (i1.getMin() < i2.getMin()) {
			new_min = i2.getMin();
		} else {
			new_min = i1.getMin();
		}

		if (i1.getMax() > i2.getMax()) {
			new_max = i2.getMax();
		} else {
			new_max = i1.getMax();
		}

		return new IntegerInterval(new_min, new_max);
	}

	/** 数学运算：加法 */
	public static IntegerDomain add(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		
		if (a.unknown || b.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				r.mergeWith(IntegerInterval.add(i1, i2));
			}
		}
		return r;
	}

	/** 数学运算：加法 */
	public static IntegerDomain add(IntegerDomain a, int x) {
		IntegerDomain r=null;
		
		if (a.unknown ) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i : a.intervals) {
			r.mergeWith(IntegerInterval.add(i, x));
		}
		return r;
	}

	/** 数学运算：减法 */
	public static IntegerDomain sub(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		if (a.unknown || b.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				r.mergeWith(IntegerInterval.sub(i1, i2));
			}
		}
		return r;
	}

	/** 数学运算：减法 */
	public static IntegerDomain sub(IntegerDomain a, int x) {
		IntegerDomain r=null;
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i : a.intervals) {
			r.mergeWith(IntegerInterval.sub(i, x));
		}
		return r;
	}

	/** 数学运算：乘法 */
	public static IntegerDomain mul(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		if (a.unknown || b.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				r.mergeWith(IntegerInterval.mul(i1, i2));
			}
		}
		return r;
	}

	/** 数学运算：乘法 */
	public static IntegerDomain mul(IntegerDomain a, int x) {
		IntegerDomain r=null;
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i : a.intervals) {
			r.mergeWith(IntegerInterval.mul(i, x));
		}
		return r;
	}

	/** 数学运算：除法 */
	public static IntegerDomain div(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		if (a.unknown || b.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				r.mergeWith(IntegerInterval.div(i1, i2));
			}
		}
		return r;
	}

	/** 数学运算：除法 */
	public static IntegerDomain div(IntegerDomain a, int x) {
		IntegerDomain r=null;
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i : a.intervals) {
			r.mergeWith(IntegerInterval.div(i, x));
		}
		return r;
	}

	/** 数学运算：整除（不精确） */
	public static IntegerDomain mod(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		if (a.unknown || b.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				r.mergeWith(IntegerInterval.mod(i1, i2));
			}
		}
		return r;
	}

	/** 数学运算：整除 */
	public static IntegerDomain mod(IntegerDomain a, int x) {
		IntegerDomain r=null;
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i : a.intervals) {
			r.mergeWith(IntegerInterval.mod(i, x));
		}
		return r;
	}

	/** 取负 */
	public static IntegerDomain uminus(IntegerDomain a) {
		IntegerDomain r=null;
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		r=new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			r.mergeWith(IntegerInterval.uminus(i1));
		}
		return r;
	}

	/** 域上求并集 r=a并b */
	public static IntegerDomain union(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		if (Config.DOMAIN_CONSERVATIVE) {
			if (a.unknown || b.unknown) {
				r = IntegerDomain.getUnknownDomain();
				return r;
			}
		}else{
			if (a.unknown) {
				r = (IntegerDomain) b.copy();
				return r;
			}
			if (b.unknown) {
				r = (IntegerDomain) a.copy();
				return r;
			}
		}

		r=new IntegerDomain(a);
		for (IntegerInterval i : b.intervals) {
			r.mergeWith(i);
		}
		return r;
	}

	/** 域上求交集 r=a交b */
	public static IntegerDomain intersect(IntegerDomain a, IntegerDomain b) {
		IntegerDomain r=null;
		
		if (a==null||a.unknown) {
			r = (IntegerDomain) b.copy();
			return r;
		}
		if (b==null||b.unknown) {
			r = (IntegerDomain) a.copy();
			return r;
		}
		
		r = new IntegerDomain();
		for (IntegerInterval i1 : a.intervals) {
			for (IntegerInterval i2 : b.intervals) {
				IntegerInterval i3 = intersectionOf(i1, i2);
				r.mergeWith(i3);
			}
		}
		return r;
	}

	/** 域上集合相减 r=e-a */
	public static IntegerDomain subtract(IntegerDomain e, IntegerDomain a) {
		IntegerDomain r = inverse(a);
		r = IntegerDomain.intersect(e, r);
		return r;
	}

	/** 域上求补集 r=~a */
	public static IntegerDomain inverse(IntegerDomain a) {
		IntegerDomain r=null;
		
		if (a.unknown) {
			r = IntegerDomain.getUnknownDomain();
			return r;
		}
		
		r= new IntegerDomain();
		if (a.intervals.isEmpty()) {
			r.mergeWith(IntegerInterval.fullInterval());
		} else {
			Iterator<IntegerInterval> interval_i = a.intervals.iterator();
			IntegerInterval first_interval = (IntegerInterval) interval_i.next();
			if (first_interval.getMin() != Long.MIN_VALUE) {
				r.intervals.add(new IntegerInterval(Long.MIN_VALUE, first_interval.getMin() - 1));
			}
			long last_max = first_interval.getMax();
			while (interval_i.hasNext()) {
				IntegerInterval interval = (IntegerInterval) interval_i.next();
				if(last_max!=Long.MAX_VALUE){
					r.intervals.add(new IntegerInterval(last_max + 1, interval.getMin() - 1));
				}
				last_max = interval.getMax();
			}
			if (last_max != Long.MAX_VALUE) {
				r.intervals.add(new IntegerInterval(last_max + 1, Long.MAX_VALUE));
			}
		}

		return r;
	}

	public void setIntervals(TreeSet<IntegerInterval> intervals) {
		this.intervals = intervals;
	}
	public static IntegerDomain valueOf(String str) {
		String[] intervals = str.split("U");
		IntegerDomain domain  = new IntegerDomain();
		for (int i = 0; i < intervals.length; i++) {
			String temp  =intervals[i].replace("[", "");
			temp = temp.replace("]", "");
			int index = temp.indexOf(",");
			long min = 0;
			if (temp.substring(0, index).trim().equals("-inf")) {
				min = DEFAULT_MIN;
			} else {
				min = Integer.parseInt(temp.substring(0, index).trim());
			}
			long max = 0;
			if (temp.substring(index+1).trim().equals("inf")) {
				max = DEFAULT_MAX;
			} else {
				max =Integer.parseInt(temp.substring(index+1).trim());
			}
			IntegerInterval interval = new IntegerInterval(min, max);
			domain.mergeWith(interval);
		}
		return domain;
	}
	
	public List<Integer> getNums()
	{
		int num=0;
		List<Integer> nums=new ArrayList<Integer>();
		for(IntegerInterval interval:intervals){
			if(num==Config.MaxArray)
			{
				return nums;
			}
			for(int i=(int)interval.getMin();i<=(int)interval.getMax();i++)
			{
				nums.add(new Integer((int)i));
				num++;
			}
		}	
		return nums;
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
