package softtest.domain.c.symbolic;

public abstract class NumberFactor extends Factor implements Cloneable{
	public abstract NumberFactor numAdd(NumberFactor o);
	
	public abstract NumberFactor numSub(NumberFactor o);
	
	public abstract NumberFactor numMul(NumberFactor o);
	
	public abstract NumberFactor numDiv(NumberFactor o);
	
	public abstract NumberFactor numMinus();
	
	public abstract double getDoubleValue();

	@Override
	public Object clone() throws CloneNotSupportedException {
		return super.clone();
	}

}
