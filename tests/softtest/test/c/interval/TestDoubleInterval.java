package softtest.test.c.interval;

import static org.junit.Assert.*;

import org.junit.Test;

import softtest.domain.c.interval.DoubleInterval;
import softtest.domain.c.interval.DoubleMath;

public class TestDoubleInterval {

	@Test(expected=RuntimeException.class)
	public void testDoubleIntervalDouble1() {
		DoubleInterval d=new DoubleInterval(5);
		assertEquals(5,d.getMax(),0);
		assertEquals(5,d.getMin(),0);
		d=new DoubleInterval(Double.NaN);
		d=new DoubleInterval(Double.NEGATIVE_INFINITY);
		d=new DoubleInterval(Double.POSITIVE_INFINITY);
	}
	
	@Test(expected=RuntimeException.class)
	public void testDoubleIntervalDouble2() {
		DoubleInterval d=new DoubleInterval(Double.POSITIVE_INFINITY);
		d.getMin();
	}
	
	@Test(expected=RuntimeException.class)
	public void testDoubleIntervalDouble3() {
		DoubleInterval d=new DoubleInterval(Double.NEGATIVE_INFINITY);
		d.getMin();
	}
	
	@Test(expected=RuntimeException.class)
	public void testDoubleIntervalDoubleDouble() {
		DoubleInterval d=new DoubleInterval(2,5);
		assertEquals(5,d.getMax(),0);
		assertEquals(2,d.getMin(),0);
		d=new DoubleInterval(Double.NaN,5);
	}

	@Test(expected=RuntimeException.class)
	public void testDoubleIntervalDoubleDoubleBooleanBoolean() {
		DoubleInterval d=new DoubleInterval(1,5,false,false);
		assertEquals(5,d.getMax(),0);
		assertEquals(1,d.getMin(),0);
		d=new DoubleInterval(1,5,true,true);
		assertEquals(DoubleMath.prevfp(5),d.getMax(),0);
		assertEquals(DoubleMath.nextfp(1),d.getMin(),0);
		d=new DoubleInterval(Double.NaN,5,false,false);
	}

	@Test
	public void testDoubleIntervalDoubleInterval() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(d1);
		assertEquals(5,d2.getMax(),0);
		assertEquals(1,d2.getMin(),0);
		assertEquals(d1,d2);
	}

	@Test
	public void testEqualsObject() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(1,5,false,false);
		assertEquals(d1,d2);
		d1=new DoubleInterval(10,5,false,false);
		d2=new DoubleInterval(100,50,false,false);
		assertEquals(d1,d2);
		assertFalse(null,d1.equals(null));
		assertTrue(null,d1.equals(d1));
		d1=new DoubleInterval(5,50,false,false);
		d2=new DoubleInterval(5,500,false,false);
		assertFalse(null,d1.equals(d2));
	}

	@Test
	public void testToString() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		assertEquals("[1.0,5.0]",d1.toString());
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY,false,false);
		assertEquals("[-Infinity,Infinity]",d1.toString());
	}

	@Test
	public void testCompareTo() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		assertEquals(new Integer(-1),new Integer(d1.compareTo(d2)));
		assertEquals(new Integer(1),new Integer(d2.compareTo(d1)));
		assertEquals(new Integer(0),new Integer(d1.compareTo(d1)));
	}

	@Test
	public void testEmptyInterval() {
		DoubleInterval d2=DoubleInterval.emptyInterval();
		assertTrue(null,d2.isEmpty());
	}

	@Test
	public void testFullInterval() {
		DoubleInterval d=DoubleInterval.fullInterval();
		assertEquals("[-Infinity,Infinity]",d.toString());
	}

	@Test
	public void testIsEmpty() {
		DoubleInterval d=new DoubleInterval(1,5,false,false);
		assertFalse(null,d.isEmpty());
		d=new DoubleInterval(2,1);
		assertTrue(null,d.isEmpty());
	}

	@Test
	public void testCanBeJoined() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
		
		d1=new DoubleInterval(-1,0,false,false);
		d2=new DoubleInterval(2,5,false,false);
		assertFalse(null,DoubleInterval.canBeJoined(d1, d2));
		assertFalse(null,DoubleInterval.canBeJoined(d2, d1));
		
		d1=new DoubleInterval(-1,0,false,false);
		d2=new DoubleInterval(0,5,false,false);
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
		
		d1=new DoubleInterval(-1,9,false,false);
		d2=new DoubleInterval(0,5,false,false);
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
		
		d1=new DoubleInterval(2,9,false,false);
		d2=new DoubleInterval(0,5,false,false);		
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
		
		d1=new DoubleInterval(5,9,false,false);
		d2=new DoubleInterval(0,5,false,false);		
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));	
		
		d1=new DoubleInterval(11,9,false,false);
		d2=new DoubleInterval(0,5,false,false);		
		assertFalse(null,DoubleInterval.canBeJoined(d1, d2));		
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,9,false,false);
		d2=new DoubleInterval(Double.NEGATIVE_INFINITY,5,false,false);		
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleInterval(0,Double.POSITIVE_INFINITY,false,false);		
		assertTrue(null,DoubleInterval.canBeJoined(d1, d2));
	}

	@Test
	public void testIsCanonical() {
		DoubleInterval d=new DoubleInterval(5,5,false,false);
		assertTrue(null,d.isCanonical());
		d=new DoubleInterval(1,5,false,false);
		assertFalse(null,d.isCanonical());
		d=DoubleInterval.emptyInterval();
		assertFalse(null,d.isCanonical());
	}

	@Test
	public void testContains() {
		DoubleInterval d=new DoubleInterval(1,5,false,false);
		assertTrue(null,d.contains(3));
		assertTrue(null,d.contains(5));
		assertFalse(null,d.contains(5.1));
		d=DoubleInterval.emptyInterval();
		assertFalse(null,d.contains(3));
	}

	@Test
	public void testIntersect() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.intersect(d1, d2);
		assertEquals(new DoubleInterval(2,5),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(2,8,false,false);
		d3=DoubleInterval.intersect(d1, d2);
		assertEquals(new DoubleInterval(2,5),d3);
		
		d1=new DoubleInterval(5,9,false,false);
		d2=new DoubleInterval(2,4,false,false);
		d3=DoubleInterval.intersect(d1, d2);
		assertEquals(DoubleInterval.emptyInterval(),d3);	
		
		d1=new DoubleInterval(5,9,false,false);
		d2=new DoubleInterval(2,5,false,false);
		d3=DoubleInterval.intersect(d1, d2);
		assertEquals(new DoubleInterval(5),d3);
		
		d1=new DoubleInterval(1,2,false,false);
		d2=new DoubleInterval(2,5,false,false);
		d3=DoubleInterval.intersect(d1, d2);
		assertEquals(new DoubleInterval(2),d3);		

		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleInterval(2,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.intersect(d1, d2);
		assertEquals(new DoubleInterval(2,Double.POSITIVE_INFINITY),d3);			
	}

	@Test
	public void testUnion() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(1,5),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(2,8,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(1,8),d3);
		
		d1=new DoubleInterval(5,9,false,false);
		d2=new DoubleInterval(2,4,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(2,9),d3);	
		
		d1=new DoubleInterval(5,9,false,false);
		d2=new DoubleInterval(2,5,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(2,9),d3);
		
		d1=new DoubleInterval(1,2,false,false);
		d2=new DoubleInterval(2,5,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(1,5),d3);		

		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d2=new DoubleInterval(2,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(new DoubleInterval(1,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(2,1,false,false);
		d2=new DoubleInterval(5,3,false,false);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(DoubleInterval.emptyInterval(),d3);	
		
		d1.setMin(0);
		d1.setMax(5);
		d3=DoubleInterval.union(d1, d2);
		assertEquals(d1,d3);	
	}

	@Test
	public void testAddDoubleIntervalDoubleInterval() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.add(d1, d2);
		assertEquals(new DoubleInterval(3,10),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.add(d1, 3);
		assertEquals(new DoubleInterval(4,8),d3);
		
		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.add(d1, 3);
		assertEquals(new DoubleInterval(4,Double.POSITIVE_INFINITY),d3);	
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.add(d1, -3);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,-2),d3);	
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.add(d1, d2);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.add(d2, d1);
		assertEquals(new DoubleInterval(1,-2),d3);	
	}

	@Test
	public void testSubDoubleIntervalDoubleInterval() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.sub(d1, d2);
		assertEquals(new DoubleInterval(-4,3),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.sub(d1, 3);
		assertEquals(new DoubleInterval(-2,2),d3);
		
		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.sub(d1, 3);
		assertEquals(new DoubleInterval(-2,Double.POSITIVE_INFINITY),d3);	
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.sub(d1, -3);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,4),d3);	
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.sub(d1, d2);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.sub(d2, d1);
		assertEquals(new DoubleInterval(1,-2),d3);	
		
		

	}

	@Test
	public void testMulDoubleIntervalDoubleInterval() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(2,25),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.mul(d1, 3);
		assertEquals(new DoubleInterval(3,15),d3);
		
		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.mul(d1, 3);
		assertEquals(new DoubleInterval(3,Double.POSITIVE_INFINITY),d3);	
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.mul(d1, -3);
		assertEquals(new DoubleInterval(-3,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.mul(d1, 3);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,3),d3);	
		
		d1=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);
		
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(0,0),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(1,25),d3);		
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-50,-1),d3);			
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-50,50),d3);			
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(1,25),d3);		
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(-50,-1),d3);			
		
		d1=new DoubleInterval(1,5,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(-50,50),d3);		

		d1=new DoubleInterval(-1,5,false,false);
		d2=new DoubleInterval(-1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-10,50),d3);	
		
		d1=new DoubleInterval(-1,5,false,false);
		d2=new DoubleInterval(-1,10,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(-10,50),d3);		
		
		d1=new DoubleInterval(-10,-5,false,false);
		d2=new DoubleInterval(-1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,10),d3);	
		
		d1=new DoubleInterval(-10,-5,false,false);
		d2=new DoubleInterval(-1,10,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(-100,10),d3);			
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.mul(d2, d1);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		//6*6种组合
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(1,100),d3);		
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);			
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);		
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,-1),d3);	
		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);			
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);			
		

		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);		
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);			
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);		
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);				
		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);		
		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);			
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);			
				
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,-1),d3);		
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,0),d3);			
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(-100,100),d3);
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,100),d3);		
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.mul(d1, d2);
		assertEquals(new DoubleInterval(1,100),d3);			
		
	}

	@Test
	public void testDivDoubleIntervalDoubleInterval() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=new DoubleInterval(2,5,false,false);
		DoubleInterval d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0.2,2.5),d3);
		
		d1=new DoubleInterval(1,5,false,false);
		d3=DoubleInterval.div(d1, 2);
		assertEquals(new DoubleInterval(0.5,2.5),d3);
		
		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d3=DoubleInterval.div(d1, 2);
		assertEquals(new DoubleInterval(0.5,Double.POSITIVE_INFINITY),d3);	
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.div(d1, -2);
		assertEquals(new DoubleInterval(-0.5,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d3=DoubleInterval.div(d1, 3);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,1.0/3),d3);
		
		d1=new DoubleInterval(-1,1,false,false);
		d2=new DoubleInterval(-1,1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(DoubleInterval.fullInterval(),d3);		
		
		d1=new DoubleInterval(-1,1,false,false);
		d2=new DoubleInterval(-1,1,false,false);
		d3=DoubleInterval.div(d2, d1);
		assertEquals(DoubleInterval.fullInterval(),d3);	
				
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		d3=DoubleInterval.div(d2, d1);
		assertEquals(new DoubleInterval(1,-2),d3);		
				
		//6*6种组合
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval((double)1/10,(double)10/1),d3);		
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval((double)1/10,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,-(double)1/10),d3);		
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.POSITIVE_INFINITY,Double.NEGATIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(1,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,-(double)1/10),d3);	
		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,(double)10/1),d3);		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,0),d3);		
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(0,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,0),d3);			
		

		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,(double)10/1),d3);		
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(-10,10,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,(double)10/1),d3);				
		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-0.0,0.0),d3);
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-0.0,0.0),d3);		
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);			
		
		d1=new DoubleInterval(0,0,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,0),d3);		
		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,0),d3);		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,0),d3);			
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0.0,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,0),d3);			
		
		d1=new DoubleInterval(-10,0,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(0,(double)10/1),d3);			
				
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(1,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(-(double)10/1,-(double)1/10),d3);		
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(0,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,-(double)1/10),d3);			
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,10,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),d3);
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval((double)1/10,Double.POSITIVE_INFINITY),d3);		
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(0,0,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,Double.NEGATIVE_INFINITY),d3);			
		
		d1=new DoubleInterval(-10,-1,false,false);
		d2=new DoubleInterval(-10,-1,false,false);
		d3=DoubleInterval.div(d1, d2);
		assertEquals(new DoubleInterval((double)1/10,(double)10/1),d3);		
	}

	@Test
	public void testUminus() {
		DoubleInterval d1=new DoubleInterval(1,5,false,false);
		DoubleInterval d2=DoubleInterval.uminus(d1);
		assertEquals(new DoubleInterval(-5,-1),d2);
		
		d1=new DoubleInterval(1,Double.POSITIVE_INFINITY,false,false);
		d2=DoubleInterval.uminus(d1);
		assertEquals(new DoubleInterval(Double.NEGATIVE_INFINITY,-1),d2);	
		
		d1=new DoubleInterval(Double.NEGATIVE_INFINITY,1,false,false);
		d2=DoubleInterval.uminus(d1);
		assertEquals(new DoubleInterval(-1,Double.POSITIVE_INFINITY),d2);
		
		d1=DoubleInterval.emptyInterval();
		d2=DoubleInterval.uminus(d1);
		assertEquals(DoubleInterval.emptyInterval(),d2);
	}

	@Test
	public void testModDoubleIntervalInt() {
		DoubleInterval d1=new DoubleInterval(5,5,false,false);
		DoubleInterval d2=DoubleInterval.mod(d1,2);
		assertEquals(new DoubleInterval(1,1),d2);
		
		d1=new DoubleInterval(10,10,false,false);
		d2=DoubleInterval.mod(d1,4);
		assertEquals(new DoubleInterval(2,2),d2);	
		
		d1=new DoubleInterval(10,10,false,false);
		d2=DoubleInterval.mod(d1,-4);
		assertEquals(new DoubleInterval(2,2),d2);
		
		d1=new DoubleInterval(5,1,false,false);
		d2=new DoubleInterval(1,1,false,false);
		DoubleInterval d3=DoubleInterval.mod(d2, d1);
		assertEquals(new DoubleInterval(1,-2),d3);		
		
		d1=new DoubleInterval(10,10,false,false);
		d2=DoubleInterval.mod(d1,new DoubleInterval(4,4));
		assertEquals(new DoubleInterval(2,2),d2);	
	}

	@Test
	public void testExceptionalCase() {
		DoubleInterval a1[]=new DoubleInterval[]{
				new DoubleInterval(Double.NEGATIVE_INFINITY,-1),new DoubleInterval(Double.NEGATIVE_INFINITY,0),
				new DoubleInterval(Double.NEGATIVE_INFINITY,1),new DoubleInterval(Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY),
				new DoubleInterval(-1,Double.POSITIVE_INFINITY),new DoubleInterval(0,Double.POSITIVE_INFINITY),
				new DoubleInterval(1,Double.POSITIVE_INFINITY),
		};
		DoubleInterval d3=null;
		d3=new DoubleInterval(Double.POSITIVE_INFINITY,Double.POSITIVE_INFINITY);
		d3=DoubleInterval.sub(d3, d3);
		for(DoubleInterval d1:a1){
			for(DoubleInterval d2:a1){
				d3=DoubleInterval.add(d1, d2);
				d3=DoubleInterval.add(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.mul(d1, d2);
				d3=DoubleInterval.mul(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.div(d1, d2);
				d3=DoubleInterval.div(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.sub(d1, d2);
				d3=DoubleInterval.sub(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.add(d1, d2);
				d3=DoubleInterval.add(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.mul(d1, d2);
				d3=DoubleInterval.mul(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
				
				d3=DoubleInterval.div(d1, d2);
				d3=DoubleInterval.div(d2, d1);
				assertFalse(d3.toString().contains("NaN"));
			}	
		}
	}
}
