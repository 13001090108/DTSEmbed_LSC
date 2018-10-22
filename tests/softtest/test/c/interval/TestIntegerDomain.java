package softtest.test.c.interval;

import static org.junit.Assert.*;

import org.junit.Test;

import softtest.domain.c.interval.IntegerDomain;
import softtest.domain.c.interval.IntegerInterval;


public class TestIntegerDomain {

	@Test
	public void testIntegerDomain() {
		IntegerDomain d1=new IntegerDomain();
		assertTrue(d1.isEmpty());
		assertFalse(d1.isCanonical());
		assertEquals(d1.getIntervals().size(),0);
	}

	@Test
	public void testIntegerDomainLongLongBooleanBoolean() {
		IntegerDomain d1=new IntegerDomain(1,5,false,false);
		assertFalse(d1.isEmpty());
		assertFalse(d1.isCanonical());
		
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testIntegerDomainLongLong(){
		IntegerDomain d1=new IntegerDomain(1,5);
		assertFalse(d1.isEmpty());
		assertFalse(d1.isCanonical());
		
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}
	
	@Test
	public void testIntegerDomainIntegerIntervalArray() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(19,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),3);
	}

	@Test
	public void testIntegerDomainIntegerInterval() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval(1,5));
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerDomain(1,5,false,false));
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testIsEmpty() {
		IntegerDomain d1=new IntegerDomain();
		assertTrue(d1.isEmpty());
		
		d1=new IntegerDomain(new IntegerInterval(1,-1));
		assertTrue(d1.isEmpty());
		
		d1=new IntegerDomain(new IntegerInterval(-3,-1));
		assertFalse(d1.isEmpty());
	}

	@Test
	public void testContainsIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(1,10,false,false);
		IntegerDomain d2=new IntegerDomain(5,8,false,false);
		assertTrue(d1.contains(d2));
		assertTrue(d1.contains(9));
		
		assertFalse(d2.contains(d1));
		assertFalse(d2.contains(9));
		
		assertTrue(d1.contains(d2));
	}

	@Test
	public void testIsCanonical() {
		IntegerDomain d1=new IntegerDomain(1,10,false,false);
		assertFalse(d1.isCanonical());
		d1=new IntegerDomain(1,1,false,false);
		assertTrue(d1.isCanonical());
	}

	@Test
	public void testEqualsObject() {
		IntegerDomain d1=new IntegerDomain(1,10,false,false);
		IntegerDomain d2=new IntegerDomain(5,8,false,false);
		
		assertFalse(d1.equals(d2));
		assertTrue(d1.equals(d1));
		
		d2=new IntegerDomain(1,10,false,false);
		assertTrue(d1.equals(d2));
		
		assertFalse(d1.equals(null));
		
		d1=new IntegerDomain();
		d2=new IntegerDomain();
		assertTrue(d1.equals(d2));
		
		d1=new IntegerDomain();
		d2=new IntegerDomain(5,8);
		assertFalse(d1.equals(d2));
	}

	@Test
	public void testToString() {
		IntegerDomain d1=new IntegerDomain(1,10,false,false);
		assertEquals("[1,10]",d1.toString());
		
		d1=new IntegerDomain(1,10,false,false);
		assertEquals("[1,10]",d1.toString());
		
		d1=new IntegerDomain(10,1,false,false);
		assertEquals("emptydomain",d1.toString());
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		assertEquals("[1,5]U[7,10]U[15,19]",d1.toString());
	}

	@Test
	public void testJointoOneInterval() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		assertEquals(new IntegerInterval(1,19,false,false),d1.jointoOneInterval());
	}

	@Test
	public void testMergeWith() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain(d1);
		d1.mergeWith(new IntegerInterval(2,1));
		assertEquals(d2,d1);
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19),new IntegerInterval(20,22)}
		);
		d1.mergeWith(new IntegerInterval(20,22));
		assertEquals(d2,d1);
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(0,6),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d1.mergeWith(new IntegerInterval(0,6));
		assertEquals(d2,d1);
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(0,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(0,10),new IntegerInterval(15,19)}
		);
		d1.mergeWith(new IntegerInterval(4,8));
		assertEquals(d2,d1);	
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(Long.MIN_VALUE,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d1.mergeWith(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE));
		assertEquals(d1,new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE));
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE)}
		);
		d1.mergeWith(new IntegerInterval(Long.MIN_VALUE,5));
		assertEquals(d1,new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE));
	}

	@Test
	public void testAddIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.add(d1, d2);
		
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(0,5,false,false);
		d3=IntegerDomain.add(d2, d1);
		assertEquals(new IntegerDomain(0,10,false,false),d3);
		
		d1=new IntegerDomain(0,5,false,false);
		d3=IntegerDomain.add(d1, 3);
		assertEquals(new IntegerDomain(3,8,false,false),d3);
			
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(5,0,false,false);
		d3=IntegerDomain.add(d2, d1);
		assertEquals(new IntegerDomain(5,0,false,false),d3);
	}

	@Test
	public void testSubIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.sub(d1, d2);
		
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(0,5,false,false);
		d3=IntegerDomain.sub(d2, d1);
		assertEquals(new IntegerDomain(-5,5,false,false),d3);
		
		d1=new IntegerDomain(0,5,false,false);
		d3=IntegerDomain.sub(d1, 4);
		assertEquals(new IntegerDomain(-4,1,false,false),d3);
			
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(5,0,false,false);
		d3=IntegerDomain.sub(d2, d1);
		assertEquals(new IntegerDomain(5,0,false,false),d3);
	}

	@Test
	public void testMulIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.mul(d1, d2);
			
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(0,5,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(0,25,false,false),d3);
		
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(5,0,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(5,0,false,false),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d3=IntegerDomain.mul(d1, 3);
		assertEquals(new IntegerDomain(3,15,false,false),d3);
		
		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d3=IntegerDomain.mul(d1, 3);
		assertEquals(new IntegerDomain(3,Long.MAX_VALUE,false,false),d3);	
		
		d1=new IntegerDomain(Long.MIN_VALUE,1,false,false);
		d3=IntegerDomain.mul(d1, -3);
		assertEquals(new IntegerDomain(-3,Long.MAX_VALUE,false,false),d3);
		
		d1=new IntegerDomain(Long.MIN_VALUE,1,false,false);
		d3=IntegerDomain.mul(d1, 3);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,3),d3);	
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(5,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);
		
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(0,0),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(1,5,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(1,25),d3);		
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-50,-1),d3);			
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-50,50),d3);			
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(1,5,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(1,25),d3);		
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(-50,-1),d3);			
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(-50,50),d3);		

		d1=new IntegerDomain(-1,5,false,false);
		d2=new IntegerDomain(-1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-10,50),d3);	
		
		d1=new IntegerDomain(-1,5,false,false);
		d2=new IntegerDomain(-1,10,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(-10,50),d3);		
		
		d1=new IntegerDomain(-10,-5,false,false);
		d2=new IntegerDomain(-1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,10),d3);	
		
		d1=new IntegerDomain(-10,-5,false,false);
		d2=new IntegerDomain(-1,10,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(-100,10),d3);			
		
		d1=new IntegerDomain(5,1,false,false);
		d2=new IntegerDomain(1,1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(1,-2),d3);		
		
		d1=new IntegerDomain(5,1,false,false);
		d2=new IntegerDomain(1,1,false,false);
		d3=IntegerDomain.mul(d2, d1);
		assertEquals(new IntegerDomain(1,-2),d3);		
		
		//6*6种组合
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(1,100),d3);		
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);			
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);		
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,-1),d3);	
		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);			
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);			
		

		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);		
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);			
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);		
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);				
		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);		
		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);			
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);			
				
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,-1),d3);		
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,0),d3);			
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(-100,100),d3);
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,100),d3);		
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.mul(d1, d2);
		assertEquals(new IntegerDomain(1,100),d3);	
	}

	@Test
	public void testDivIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.div(d1, d2);
		
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(1,5,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,5,false,false),d3);
		
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(5,0,false,false);
		d3=IntegerDomain.div(d2, d1);
		assertEquals(new IntegerDomain(5,0,false,false),d3);
		
		
		d1=new IntegerDomain(1,5,false,false);
		d3=IntegerDomain.div(d1, 2);
		assertEquals(new IntegerDomain(0,2),d3);
		
		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d3=IntegerDomain.div(d1, 2);
		assertEquals(new IntegerDomain(0,Long.MAX_VALUE),d3);	
		
		d1=new IntegerDomain(Long.MIN_VALUE,1,false,false);
		d3=IntegerDomain.div(d1, -2);
		assertEquals(new IntegerDomain(0,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(Long.MIN_VALUE,1,false,false);
		d3=IntegerDomain.div(d1, 3);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,0),d3);
		
		d1=new IntegerDomain(-1,1,false,false);
		d2=new IntegerDomain(-1,1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(IntegerInterval.fullInterval()),d3);		
		
		d1=new IntegerDomain(-1,1,false,false);
		d2=new IntegerDomain(-1,1,false,false);
		d3=IntegerDomain.div(d2, d1);
		assertEquals(new IntegerDomain(IntegerInterval.fullInterval()),d3);	
				
		d1=new IntegerDomain(5,1,false,false);
		d2=new IntegerDomain(1,1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(1,-2),d3);		
		
		d1=new IntegerDomain(5,1,false,false);
		d2=new IntegerDomain(1,1,false,false);
		d3=IntegerDomain.div(d2, d1);
		assertEquals(new IntegerDomain(1,-2),d3);		
				
		//6*6种组合
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(1/10,10/1),d3);		
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(1/10,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,-1/10),d3);		
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MAX_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(1,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,-1/10),d3);	
		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,10/1),d3);		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,0),d3);		
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(0,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,0),d3);			
		

		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,10/1),d3);		
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);		
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerDomain(-10,10,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,10/1),d3);				
		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-0,0),d3);
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-0,0),d3);		
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);			
		
		d1=new IntegerDomain(0,0,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,0),d3);		
		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,0),d3);		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,0),d3);			
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,Long.MAX_VALUE),d3);		
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,0),d3);			
		
		d1=new IntegerDomain(-10,0,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(0,10/1),d3);			
				
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(1,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(-10/1,-1/10),d3);		
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(0,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,-1/10),d3);			
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,10,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(1/10,Long.MAX_VALUE),d3);		
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(0,0,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MIN_VALUE),d3);			
		
		d1=new IntegerDomain(-10,-1,false,false);
		d2=new IntegerDomain(-10,-1,false,false);
		d3=IntegerDomain.div(d1, d2);
		assertEquals(new IntegerDomain(1/10,10/1),d3);	
	}

	@Test
	public void testModIntegerDomainIntegerDomain() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.mod(d1, d2);

			
		d1=new IntegerDomain(0,5,false,false);
		d2=new IntegerDomain(5,0,false,false);
		d3=IntegerDomain.mod(d2, d1);
		assertEquals(new IntegerDomain(5,0,false,false),d3);
		
		d1=new IntegerDomain(5,5,false,false);
		d2=IntegerDomain.mod(d1,2);
		assertEquals(new IntegerDomain(1,1),d2);
		
		d1=new IntegerDomain(10,10,false,false);
		d2=IntegerDomain.mod(d1,4);
		assertEquals(new IntegerDomain(2,2),d2);	
		
		d1=new IntegerDomain(10,10,false,false);
		d2=IntegerDomain.mod(d1,-4);
		assertEquals(new IntegerDomain(2,2),d2);
		
		d1=new IntegerDomain(5,1,false,false);
		d2=new IntegerDomain(1,1,false,false);
		d3=IntegerDomain.mod(d2, d1);
		assertEquals(new IntegerDomain(1,-2),d3);		
		
		d1=new IntegerDomain(10,10,false,false);
		d2=IntegerDomain.mod(d1,new IntegerDomain(4,4));
		assertEquals(new IntegerDomain(2,2),d2);	
	}

	@Test
	public void testUminus() {
		IntegerDomain d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		IntegerDomain d2=new IntegerDomain();
		IntegerDomain d3=IntegerDomain.uminus(d2);
		
		d3=IntegerDomain.uminus(d1);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(-5,-1),new IntegerInterval(-10,-7),new IntegerInterval(-19,-15)}),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=IntegerDomain.uminus(d1);
		assertEquals(new IntegerDomain(-5,-1),d2);
		
		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d2=IntegerDomain.uminus(d1);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,-1),d2);	
		
		d1=new IntegerDomain(Long.MIN_VALUE,1,false,false);
		d2=IntegerDomain.uminus(d1);
		assertEquals(new IntegerDomain(-1,Long.MAX_VALUE),d2);
		
		d1=new IntegerDomain();
		d2=IntegerDomain.uminus(d1);
		assertEquals(new IntegerDomain(),d2);
	}

	@Test
	public void testUnion() {
		IntegerDomain d1=new IntegerDomain(1,5,false,false);
		IntegerDomain d2=new IntegerDomain(2,5,false,false);
		IntegerDomain d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(1,5),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(2,8,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(1,8),d3);
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,4,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(2,4),new IntegerInterval(5,9)}),d3);	
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(2,9),d3);
		
		d1=new IntegerDomain(1,2,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(1,5),d3);		

		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d2=new IntegerDomain(2,Long.MAX_VALUE,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(1,Long.MAX_VALUE),d3);
		
		d1=new IntegerDomain(2,1,false,false);
		d2=new IntegerDomain(5,3,false,false);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(),d3);	
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(4,8);
		d3=IntegerDomain.union(d1, d2);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,10),new IntegerInterval(15,19)}),d3);	
	}

	@Test
	public void testIntersect() {
		IntegerDomain d1=new IntegerDomain(1,5,false,false);
		IntegerDomain d2=new IntegerDomain(2,5,false,false);
		IntegerDomain d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(2,5),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(2,5),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(2,8,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(2,5),d3);
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,4,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(),d3);	
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(5,5),d3);
		
		d1=new IntegerDomain(1,2,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(2,2),d3);		

		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d2=new IntegerDomain(2,Long.MAX_VALUE,false,false);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(2,Long.MAX_VALUE),d3);	

		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(4,8);
		d3=IntegerDomain.intersect(d1, d2);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(4,5),new IntegerInterval(7,8)}),d3);	
	}

	@Test
	public void testSubtract() {
		IntegerDomain d1=new IntegerDomain(1,5,false,false);
		IntegerDomain d2=new IntegerDomain(2,5,false,false);
		IntegerDomain d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(1,1),d3);
		
		d1=new IntegerDomain(1,5,false,false);
		d2=new IntegerDomain(2,8,false,false);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(1,1),d3);
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,4,false,false);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(5,9),d3);	
		
		d1=new IntegerDomain(5,9,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(6,9),d3);
		
		d1=new IntegerDomain(1,2,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(1,1),d3);		

		d1=new IntegerDomain(1,Long.MAX_VALUE,false,false);
		d2=new IntegerDomain(2,5,false,false);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,1),new IntegerInterval(6,Long.MAX_VALUE)}),d3);	

		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=new IntegerDomain(4,8);
		d3=IntegerDomain.subtract(d1, d2);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,3),new IntegerInterval(9,10),new IntegerInterval(15,19)}),d3);	
	}

	@Test
	public void testInverse() {
		IntegerDomain d1=new IntegerDomain(1,5,false,false);
		IntegerDomain d2=IntegerDomain.inverse(d1);
		assertEquals(new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(Long.MIN_VALUE,0),new IntegerInterval(6,Long.MAX_VALUE)}),d2);
		
		d1=new IntegerDomain(1,5);
		d2=IntegerDomain.inverse(IntegerDomain.inverse(d1));
		assertEquals(d1,d2);
		
		d1=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(1,5),new IntegerInterval(7,10),new IntegerInterval(15,19)}
		);
		d2=IntegerDomain.inverse(d1);
		IntegerDomain d3=new IntegerDomain(new IntegerInterval[]{
				new IntegerInterval(Long.MIN_VALUE,0),new IntegerInterval(6,6)
				,new IntegerInterval(11,14),new IntegerInterval(20,Long.MAX_VALUE)});
		assertEquals(d3,d2);
		
		d2=IntegerDomain.inverse(IntegerDomain.inverse(d1));
		assertEquals(d1,d2);
		
		d2=IntegerDomain.inverse(IntegerDomain.inverse(IntegerDomain.inverse(d1)));
		assertEquals(d3,d2);
		
		d2=IntegerDomain.inverse(IntegerDomain.inverse(IntegerDomain.inverse(IntegerDomain.inverse(d1))));
		assertEquals(d1,d2);
		
		d1=new IntegerDomain();
		d2=IntegerDomain.inverse(d1);
		assertEquals(new IntegerDomain(Long.MIN_VALUE,Long.MAX_VALUE),d2);
		
		d1=new IntegerDomain();
		d2=IntegerDomain.inverse(IntegerDomain.inverse(d1));
		assertEquals(new IntegerDomain(Long.MAX_VALUE,Long.MIN_VALUE),d2);
	}

}
