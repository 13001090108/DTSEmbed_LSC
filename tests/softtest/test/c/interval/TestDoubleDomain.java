package softtest.test.c.interval;

import static org.junit.Assert.*;


import org.junit.Test;

import softtest.domain.c.interval.DoubleDomain;
import softtest.domain.c.interval.DoubleInterval;
import softtest.domain.c.interval.DoubleMath;

public class TestDoubleDomain {

	@Test
	public void testDoubleDomain() {
		DoubleDomain d1=new DoubleDomain();
		assertTrue(d1.isEmpty());
		assertFalse(d1.isCanonical());
		assertEquals(d1.getIntervals().size(),0);
	}

	@Test
	public void testDoubleDomainDoubleDoubleBooleanBoolean() {
		DoubleDomain d1=new DoubleDomain(1,5,false,false);
		assertFalse(d1.isEmpty());
		assertFalse(d1.isCanonical());
		
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}
	
	@Test
	public void testDoubleDomainDoubleDouble() {
		DoubleDomain d1=new DoubleDomain(1,5);
		assertFalse(d1.isEmpty());
		assertFalse(d1.isCanonical());
		
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testDoubleDomainDoubleIntervalArray() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(19,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),3);
	}

	@Test
	public void testDoubleDomainDoubleInterval() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval(1,5));
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleDomain(1,5,false,false));
		assertEquals(1,d1.jointoOneInterval().getMin(),0);
		assertEquals(5,d1.jointoOneInterval().getMax(),0);
		assertEquals(d1.getIntervals().size(),1);
	}

	@Test
	public void testIsEmpty() {
		DoubleDomain d1=new DoubleDomain();
		assertTrue(d1.isEmpty());
		
		d1=new DoubleDomain(new DoubleInterval(1,-1));
		assertTrue(d1.isEmpty());
		
		d1=new DoubleDomain(new DoubleInterval(-3,-1));
		assertFalse(d1.isEmpty());
	}

	@Test
	public void testContainsDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(1,10,false,false);
		DoubleDomain d2=new DoubleDomain(5,8,false,false);
		assertTrue(d1.contains(d2));
		assertTrue(d1.contains(9));
		
		assertFalse(d2.contains(d1));
		assertFalse(d2.contains(9));
		
		assertTrue(d1.contains(d2));
	}

	@Test
	public void testIsCanonical() {
		DoubleDomain d1=new DoubleDomain(1,10,false,false);
		assertFalse(d1.isCanonical());
		d1=new DoubleDomain(1,1,false,false);
		assertTrue(d1.isCanonical());
	}

	@Test
	public void testEqualsObject() {
		DoubleDomain d1=new DoubleDomain(1,10,false,false);
		DoubleDomain d2=new DoubleDomain(5,8,false,false);
		
		assertFalse(d1.equals(d2));
		assertTrue(d1.equals(d1));
		
		d2=new DoubleDomain(1,10,false,false);
		assertTrue(d1.equals(d2));
		
		assertFalse(d1.equals(null));
		
		d1=new DoubleDomain();
		d2=new DoubleDomain();
		assertTrue(d1.equals(d2));
		
		d1=new DoubleDomain();
		d2=new DoubleDomain(5,8);
		assertFalse(d1.equals(d2));
	}

	@Test
	public void testToString() {
		DoubleDomain d1=new DoubleDomain(1,10,false,false);
		assertEquals("[1.0,10.0]",d1.toString());
		
		d1=new DoubleDomain(1,10,false,false);
		assertEquals("[1.0,10.0]",d1.toString());
		
		d1=new DoubleDomain(10,1,false,false);
		assertEquals("emptydomain",d1.toString());
			
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		assertEquals("[1.0,5.0]U[7.0,10.0]U[15.0,19.0]",d1.toString());
	}

	@Test
	public void testJointoOneInterval() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		assertEquals(new DoubleInterval(1,19,false,false),d1.jointoOneInterval());
	}

	@Test
	public void testMergeWith() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain(d1);
		d1.mergeWith(new DoubleInterval(2,1));
		assertEquals(d2,d1);
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19),new DoubleInterval(20,22)}
		);
		d1.mergeWith(new DoubleInterval(20,22));
		assertEquals(d2,d1);
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(0,6),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d1.mergeWith(new DoubleInterval(0,6));
		assertEquals(d2,d1);
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(0,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(0,10),new DoubleInterval(15,19)}
		);
		d1.mergeWith(new DoubleInterval(4,8));
		assertEquals(d2,d1);	
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(Double.NEGATIVE_INFINITY,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d1.mergeWith(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY));
		assertEquals(d1,new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY));
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY)}
		);
		d1.mergeWith(new DoubleInterval(Double.NEGATIVE_INFINITY,5));
		assertEquals(d1,new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY));
	}

	@Test
	public void testAddDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.add(d1, d2);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.add(d2, d1);
		assertEquals(new DoubleDomain(0,10,false,false),d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.add(d1, 3);
		assertEquals(new DoubleDomain(3,8,false,false),d3);
				
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(5,0,false,false);
		d3=DoubleDomain.add(d2, d1);
		assertEquals(new DoubleDomain(5,0,false,false),d3);
		
	}

	@Test
	public void testSubDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.sub(d1, d2);		
		
		d3=DoubleDomain.sub(d2, d1);
		assertEquals(d2,d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.sub(d2, d1);
		assertEquals(new DoubleDomain(-5,5,false,false),d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.sub(d1, 4);
		assertEquals(new DoubleDomain(-4,1,false,false),d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.sub(d1, 4);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(5,0,false,false);
		d3=DoubleDomain.sub(d2, d1);
		assertEquals(new DoubleDomain(5,0,false,false),d3);
	}

	@Test
	public void testMulDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.mul(d1, d2);	
		
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(d2,d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(0,5,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(0,25,false,false),d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(5,0,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(5,0,false,false),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.mul(d1, 3);
		assertEquals(new DoubleDomain(3,15,false,false),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.mul(d1, 3);
		
		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleDomain.mul(d1, 3);
		assertEquals(new DoubleDomain(3,Double.POSITIVE_INFINITY,false,false),d3);	
		
		d1=new DoubleDomain(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleDomain.mul(d1, -3);
		assertEquals(new DoubleDomain(-3,Double.POSITIVE_INFINITY,false,false),d3);
		
		d1=new DoubleDomain(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleDomain.mul(d1, 3);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,3),d3);	
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(5,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);
		
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(0,0),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(1,25),d3);		
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-50,-1),d3);			
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-50,50),d3);			
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(1,25),d3);		
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(-50,-1),d3);			
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(-50,50),d3);		

		d1=new DoubleDomain(-1,5,false,false);
		d2=new DoubleDomain(-1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-10,50),d3);	
		
		d1=new DoubleDomain(-1,5,false,false);
		d2=new DoubleDomain(-1,10,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(-10,50),d3);		
		
		d1=new DoubleDomain(-10,-5,false,false);
		d2=new DoubleDomain(-1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,10),d3);	
		
		d1=new DoubleDomain(-10,-5,false,false);
		d2=new DoubleDomain(-1,10,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(-100,10),d3);			
		
		d1=new DoubleDomain(5,1,false,false);
		d2=new DoubleDomain(1,1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(1,-2),d3);		
		
		d1=new DoubleDomain(5,1,false,false);
		d2=new DoubleDomain(1,1,false,false);
		d3=DoubleDomain.mul(d2, d1);
		assertEquals(new DoubleDomain(1,-2),d3);		
		
		//6*6种组合
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(1,100),d3);		
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);			
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);		
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,-1),d3);	
		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);			
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);			
		

		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);		
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);			
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);		
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);				
		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);		
		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);			
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);			
				
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,-1),d3);		
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,0),d3);			
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(-100,100),d3);
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,100),d3);		
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(1,100),d3);	
	}

	@Test
	public void testDivDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.div(d1, d2);		
		
		d3=DoubleDomain.div(d2, d1);
		assertEquals(d2,d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,5,false,false),d3);
		
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(5,0,false,false);
		d3=DoubleDomain.div(d2, d1);
		assertEquals(new DoubleDomain(5,0,false,false),d3);
		
		
		d1=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.div(d1, 2);
		assertEquals(new DoubleDomain(0.5,2.5),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d3=DoubleDomain.div(d1, 2);
		
		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleDomain.div(d1, 2);
		assertEquals(new DoubleDomain(0.5,Double.POSITIVE_INFINITY),d3);	
		
		d1=new DoubleDomain(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleDomain.div(d1, -2);
		assertEquals(new DoubleDomain(-0.5,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleDomain.div(d1, 3);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,1.0/3),d3);
		
		d1=new DoubleDomain(-1,1,false,false);
		d2=new DoubleDomain(-1,1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(DoubleInterval.fullInterval()),d3);		
		
		d1=new DoubleDomain(-1,1,false,false);
		d2=new DoubleDomain(-1,1,false,false);
		d3=DoubleDomain.div(d2, d1);
		assertEquals(new DoubleDomain(DoubleInterval.fullInterval()),d3);	
				
		d1=new DoubleDomain(5,1,false,false);
		d2=new DoubleDomain(1,1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(1,-2),d3);		
		
		d1=new DoubleDomain(5,1,false,false);
		d2=new DoubleDomain(1,1,false,false);
		d3=DoubleDomain.div(d2, d1);
		assertEquals(new DoubleDomain(1,-2),d3);		
				
		//6*6种组合
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain((double)1/10,(double)10/1),d3);		
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain((double)1/10,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,-(double)1/10),d3);		
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.POSITIVE_INFINITY,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(1,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,-(double)1/10),d3);	
		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,(double)10/1),d3);		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,0),d3);		
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(0,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,0),d3);			
		

		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,(double)10/1),d3);		
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(-10,10,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,(double)10/1),d3);				
		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-0.0,0.0),d3);
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-0.0,0.0),d3);		
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);			
		
		d1=new DoubleDomain(0,0,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);		
		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,0),d3);		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,0),d3);			
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0.0,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,0),d3);			
		
		d1=new DoubleDomain(-10,0,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,(double)10/1),d3);			
				
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(1,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(-(double)10/1,-(double)1/10),d3);		
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(0,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,-(double)1/10),d3);			
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,10,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain((double)1/10,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(0,0,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.NEGATIVE_INFINITY),d3);			
		
		d1=new DoubleDomain(-10,-1,false,false);
		d2=new DoubleDomain(-10,-1,false,false);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain((double)1/10,(double)10/1),d3);				
	}

	@Test
	public void testModDoubleDomainDoubleDomain() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.mod(d1, d2);	
		
		d3=DoubleDomain.mod(d2, d1);
		assertEquals(d2,d3);
			
		d1=new DoubleDomain(0,5,false,false);
		d2=new DoubleDomain(5,0,false,false);
		d3=DoubleDomain.mod(d2, d1);
		assertEquals(new DoubleDomain(5,0,false,false),d3);
		
		d1=new DoubleDomain(5,5,false,false);
		d2=DoubleDomain.mod(d1,2);
		assertEquals(new DoubleDomain(1,1),d2);
		
		d1=new DoubleDomain(5,5,false,false);
		d2=DoubleDomain.mod(d1,2);
		
		d1=new DoubleDomain(10,10,false,false);
		d2=DoubleDomain.mod(d1,4);
		assertEquals(new DoubleDomain(2,2),d2);	
		
		d1=new DoubleDomain(10,10,false,false);
		d2=DoubleDomain.mod(d1,-4);
		assertEquals(new DoubleDomain(2,2),d2);
		
		d1=new DoubleDomain(5,1,false,false);
		d2=new DoubleDomain(1,1,false,false);
		d3=DoubleDomain.mod(d2, d1);
		assertEquals(new DoubleDomain(1,-2),d3);		
		
		d1=new DoubleDomain(10,10,false,false);
		d2=DoubleDomain.mod(d1,new DoubleDomain(4,4));
		assertEquals(new DoubleDomain(2,2),d2);	
	}

	@Test
	public void testUminus() {
		DoubleDomain d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		DoubleDomain d2=new DoubleDomain();
		DoubleDomain d3=DoubleDomain.uminus(d2);		
		
		d3=DoubleDomain.uminus(d1);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(-5,-1),new DoubleInterval(-10,-7),new DoubleInterval(-19,-15)}),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d2=DoubleDomain.uminus(d1);
		assertEquals(new DoubleDomain(-5,-1),d2);
		
		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d2=DoubleDomain.uminus(d1);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,-1),d2);	
		
		d1=new DoubleDomain(Double.NEGATIVE_INFINITY,1,false,false);
		d2=DoubleDomain.uminus(d1);
		assertEquals(new DoubleDomain(-1,Double.POSITIVE_INFINITY),d2);
		
		d1=new DoubleDomain();
		d2=DoubleDomain.uminus(d1);
		assertEquals(new DoubleDomain(),d2);
	}

	@Test
	public void testUnion() {
		DoubleDomain d1=new DoubleDomain(1,5,false,false);
		DoubleDomain d2=new DoubleDomain(2,5,false,false);
		DoubleDomain d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(1,5),d3);
		
		d1=new DoubleDomain(1,5);
		d2=new DoubleDomain(2,5);
		d3=DoubleDomain.union(d1, d2);
		d3=DoubleDomain.union(d2, d1);
		assertEquals(d1,d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(2,8,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(1,8),d3);
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,4,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(2,4),new DoubleInterval(5,9)}),d3);	
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(2,9),d3);
		
		d1=new DoubleDomain(1,2,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(1,5),d3);		

		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleDomain(2,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(1,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleDomain(2,1,false,false);
		d2=new DoubleDomain(5,3,false,false);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(),d3);	
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(4,8);
		d3=DoubleDomain.union(d1, d2);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,10),new DoubleInterval(15,19)}),d3);		
	}

	@Test
	public void testIntersect() {
		DoubleDomain d1=new DoubleDomain(1,5,false,false);
		DoubleDomain d2=new DoubleDomain(2,5,false,false);
		DoubleDomain d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(2,5),d3);
				
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(2,5),d3);
		
		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(2,8,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(2,5),d3);
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,4,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(),d3);	
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(5,5),d3);
		
		d1=new DoubleDomain(1,2,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(2,2),d3);		

		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleDomain(2,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(2,Double.POSITIVE_INFINITY),d3);	

		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(4,8);
		d3=DoubleDomain.intersect(d1, d2);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(4,5),new DoubleInterval(7,8)}),d3);	
	}

	@Test
	public void testSubtract() {
		DoubleDomain d1=new DoubleDomain(1,5,false,false);
		DoubleDomain d2=new DoubleDomain(2,5,false,false);
		DoubleDomain d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(1,DoubleMath.prevfp(2)),d3);
		

		d1=new DoubleDomain(1,5,false,false);
		d2=new DoubleDomain(2,8,false,false);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(1,DoubleMath.prevfp(2)),d3);
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,4,false,false);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(5,9),d3);	
		
		d1=new DoubleDomain(5,9,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(DoubleMath.nextfp(5),9),d3);
		
		d1=new DoubleDomain(1,2,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(1,DoubleMath.prevfp(2)),d3);		

		d1=new DoubleDomain(1,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleDomain(2,5,false,false);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,DoubleMath.prevfp(2)),new DoubleInterval(DoubleMath.nextfp(5),Double.POSITIVE_INFINITY)}),d3);	

		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=new DoubleDomain(4,8);
		d3=DoubleDomain.subtract(d1, d2);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,DoubleMath.prevfp(4)),new DoubleInterval(DoubleMath.nextfp(8),10),new DoubleInterval(15,19)}),d3);	
	}

	@Test
	public void testInverse() {
		DoubleDomain d1=new DoubleDomain(1,5,false,false);
		DoubleDomain d2=DoubleDomain.inverse(d1);
		assertEquals(new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(1)),new DoubleInterval(DoubleMath.nextfp(5),Double.POSITIVE_INFINITY)}),d2);
		
	
		d1=new DoubleDomain(1,5);
		d2=DoubleDomain.inverse(DoubleDomain.inverse(d1));
		assertEquals(d1,d2);
		
		d1=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(1,5),new DoubleInterval(7,10),new DoubleInterval(15,19)}
		);
		d2=DoubleDomain.inverse(d1);
		DoubleDomain d3=new DoubleDomain(new DoubleInterval[]{
				new DoubleInterval(Double.NEGATIVE_INFINITY,DoubleMath.prevfp(1)),new DoubleInterval(DoubleMath.nextfp(5),DoubleMath.prevfp(7))
				,new DoubleInterval(DoubleMath.nextfp(10),DoubleMath.prevfp(15)),new DoubleInterval(DoubleMath.nextfp(19),Double.POSITIVE_INFINITY)});
		assertEquals(d3,d2);
		
		d2=DoubleDomain.inverse(DoubleDomain.inverse(d1));
		assertEquals(d1,d2);
		
		d2=DoubleDomain.inverse(DoubleDomain.inverse(DoubleDomain.inverse(d1)));
		assertEquals(d3,d2);
		
		d2=DoubleDomain.inverse(DoubleDomain.inverse(DoubleDomain.inverse(DoubleDomain.inverse(d1))));
		assertEquals(d1,d2);
		
		d1=new DoubleDomain();
		d2=DoubleDomain.inverse(d1);
		assertEquals(new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d2);
		
		d1=new DoubleDomain();
		d2=DoubleDomain.inverse(DoubleDomain.inverse(d1));
		assertEquals(new DoubleDomain(Double.POSITIVE_INFINITY,Double.NEGATIVE_INFINITY),d2);
	}

	@Test
	public void testInfinity(){
		DoubleDomain d1,d2,d3;
		
		d1=new DoubleDomain(0,0);
		d2=new DoubleDomain(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY);
		d3=DoubleDomain.mul(d1, d2);
		assertEquals(new DoubleDomain(0,0),d3);
		
		d1=new DoubleDomain(0,1);
		d2=new DoubleDomain(0,1);
		d3=DoubleDomain.div(d1, d2);
		assertEquals(new DoubleDomain(0,Double.POSITIVE_INFINITY),d3);
	}
}
