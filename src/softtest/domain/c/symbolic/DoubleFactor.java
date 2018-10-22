package softtest.domain.c.symbolic;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.DoubleDomain;
import softtest.symboltable.c.Type.CType_BaseType;

public class DoubleFactor extends NumberFactor {
	private double value=0.0;
		
	public DoubleFactor(double value) {
		this.value = value;
		this.type=CType_BaseType.getBaseType("double");
	}

	public double getValue() {
		return value;
	}

	public void setValue(double value) {
		this.value = value;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		long temp;
		temp = Double.doubleToLongBits(value);
		result = prime * result + (int) (temp ^ (temp >>> 32));
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
		DoubleFactor other = (DoubleFactor) obj;
		if (Double.doubleToLongBits(value) != Double
				.doubleToLongBits(other.value))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return ""+value;
	}

	@Override
	public int compareTo(Factor o) {
		if(o instanceof NumberFactor){
			return 0;
		}
		return -1;
	}

	@Override
	public NumberFactor numAdd(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(other.getValue()+value);
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new DoubleFactor((double)other.getValue()+value);
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numSub(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(value-other.getValue());
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new DoubleFactor(value-(double)other.getValue());
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numMul(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(other.getValue()*value);
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new DoubleFactor((double)other.getValue()*value);
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numDiv(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(value/other.getValue());
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new DoubleFactor(value/(double)other.getValue());
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numMinus() {
		return new DoubleFactor(-value);
	}

	@Override
	public double getDoubleValue() {
		return value;
	}

	@Override
	public Domain getDomain(SymbolDomainSet ds) {
		return new DoubleDomain(value,value);
	}
}
