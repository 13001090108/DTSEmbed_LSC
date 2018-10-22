package softtest.test.c.interval;

import static org.junit.Assert.*;

import org.junit.Test;

import softtest.domain.c.interval.IntegerInterval;

public class TestIntegerInterval {

	@Test
	public void testIntegerIntervalLongLong() {
		IntegerInterval d=new IntegerInterval(1,5);
		assertEquals(5,d.getMax(),0);
		assertEquals(1,d.getMin(),0);
	}

	@Test
	public void testIntegerIntervalLong() {
		IntegerInterval d=new IntegerInterval(5);
		assertEquals(5,d.getMax(),0);
		assertEquals(5,d.getMin(),0);
	}

	@Test
	public void testIntegerIntervalLongLongBooleanBoolean() {
		IntegerInterval d=new IntegerInterval(1,5,false,false);
		assertEquals(5,d.getMax(),0);
		assertEquals(1,d.getMin(),0);
		d=new IntegerInterval(1,5,true,true);
		assertEquals(4,d.getMax(),0);
		assertEquals(2,d.getMin(),0);
	}

	@Test
	public void testIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(d1);
		assertEquals(5,d2.getMax(),0);
		assertEquals(1,d2.getMin(),0);
		assertEquals(d1,d2);
	}

	@Test
	public void testEqualsObject() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(1,5,false,false);
		assertEquals(d1,d2);
		d1=new IntegerInterval(10,5,false,false);
		d2=new IntegerInterval(100,50,false,false);
		assertEquals(d1,d2);
		d2=null;
		assertFalse(d1.equals(d2));
		assertFalse(d1.equals(new Object()));
		assertTrue(d1.equals(d1));
		d1=new IntegerInterval(5,10,false,false);
		d2=new IntegerInterval(5,50,false,false);
		assertFalse(d1.equals(d2));
		d1=new IntegerInterval(6,500,false,false);
		d2=new IntegerInterval(5,50,false,false);
		assertFalse(d1.equals(d2));
		
		assertFalse(null,d1.equals(null));
		assertTrue(null,d1.equals(d1));
		d1=new IntegerInterval(5,50,false,false);
		d2=new IntegerInterval(5,500,false,false);
		assertFalse(null,d1.equals(d2));
	}

	@Test
	public void testToString() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		assertEquals("[1,5]",d1.toString());
		d1=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE,false,false);
		assertEquals("[-inf,inf]",d1.toString());
		d1=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE,true,true);
		assertEquals("[-inf,inf]",d1.toString());		
	}

	@Test
	public void testCompareTo() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		assertEquals(new Integer(-1),new Integer(d1.compareTo(d2)));
		assertEquals(new Integer(1),new Integer(d2.compareTo(d1)));
		assertEquals(new Integer(0),new Integer(d1.compareTo(d1)));
	}
	
	@Test
	public void testSetMin(){
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		d1.setMin(-2);
		assertEquals(-2,d1.getMin(),0);
		
		d1.setMin(Long.MIN_VALUE);
		assertEquals(Long.MIN_VALUE,d1.getMin(),0);
	}
	
	@Test
	public void testSetMax(){
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		d1.setMax(9);
		assertEquals(9,d1.getMax(),0);
		
		d1.setMax(Long.MAX_VALUE);
		assertEquals(Long.MAX_VALUE,d1.getMax(),0);	
	}

	@Test
	public void testEmptyInterval() {
		IntegerInterval d2=IntegerInterval.emptyInterval();
		assertTrue(null,d2.isEmpty());
	}

	@Test
	public void testFullInterval() {
		IntegerInterval d=IntegerInterval.fullInterval();
		assertEquals("[-inf,inf]",d.toString());
	}

	@Test
	public void testIsEmpty() {
		IntegerInterval d=new IntegerInterval(1,5,false,false);
		assertFalse(null,d.isEmpty());
		d=new IntegerInterval(2,1);
		assertTrue(null,d.isEmpty());
	}

	@Test
	public void testCanBeJoined() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
		
		d1=new IntegerInterval(-1,0,false,false);
		d2=new IntegerInterval(2,5,false,false);
		assertFalse(null,IntegerInterval.canBeJoined(d1, d2));
		assertFalse(null,IntegerInterval.canBeJoined(d2, d1));
		
		d1=new IntegerInterval(-1,0,false,false);
		d2=new IntegerInterval(0,5,false,false);
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
		
		d1=new IntegerInterval(-1,9,false,false);
		d2=new IntegerInterval(0,5,false,false);
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
		
		d1=new IntegerInterval(2,9,false,false);
		d2=new IntegerInterval(0,5,false,false);		
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
		
		d1=new IntegerInterval(5,9,false,false);
		d2=new IntegerInterval(0,5,false,false);		
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));	
		
		d1=new IntegerInterval(11,9,false,false);
		d2=new IntegerInterval(0,5,false,false);		
		assertFalse(null,IntegerInterval.canBeJoined(d1, d2));		
		
		d1=new IntegerInterval(Long.MIN_VALUE,9,false,false);
		d2=new IntegerInterval(Long.MIN_VALUE,5,false,false);		
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
		
		d1=new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE,false,false);
		d2=new IntegerInterval(0,Long.MAX_VALUE,false,false);		
		assertTrue(null,IntegerInterval.canBeJoined(d1, d2));
	}

	@Test
	public void testIsCanonical() {
		IntegerInterval d=new IntegerInterval(5,5,false,false);
		assertTrue(null,d.isCanonical());
		d=new IntegerInterval(1,5,false,false);
		assertFalse(null,d.isCanonical());
		d=IntegerInterval.emptyInterval();
		assertFalse(null,d.isCanonical());
	}

	@Test
	public void testContains() {
		IntegerInterval d=new IntegerInterval(1,5,false,false);
		assertTrue(null,d.contains(3));
		assertTrue(null,d.contains(5));
		assertFalse(null,d.contains(6));
		d=IntegerInterval.emptyInterval();
		assertFalse(null,d.contains(3));
	}

	@Test
	public void testIntersect() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(2,5),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d2=new IntegerInterval(2,8,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(2,5),d3);
		
		d1=new IntegerInterval(5,9,false,false);
		d2=new IntegerInterval(2,4,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(IntegerInterval.emptyInterval(),d3);	
		
		d1=new IntegerInterval(5,9,false,false);
		d2=new IntegerInterval(2,5,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(5),d3);
		
		d1=new IntegerInterval(1,2,false,false);
		d2=new IntegerInterval(2,5,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(2),d3);		

		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d2=new IntegerInterval(2,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(2,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d2=new IntegerInterval(2,5,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(2,5),d3);		
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d2=new IntegerInterval(-2,5,false,false);
		d3=IntegerInterval.intersect(d1, d2);
		assertEquals(new IntegerInterval(-2,1),d3);				
	}

	@Test
	public void testUnion() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,5),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d2=new IntegerInterval(2,8,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,8),d3);
		
		d1=new IntegerInterval(5,9,false,false);
		d2=new IntegerInterval(2,4,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(2,9),d3);	
		
		d1=new IntegerInterval(5,9,false,false);
		d2=new IntegerInterval(2,5,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(2,9),d3);
		
		d1=new IntegerInterval(1,2,false,false);
		d2=new IntegerInterval(2,5,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,5),d3);		

		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d2=new IntegerInterval(2,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(2,1,false,false);
		d2=new IntegerInterval(1,3,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,3),d3);
		
		d1=new IntegerInterval(1,3,false,false);
		d2=new IntegerInterval(2,1,false,false);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(new IntegerInterval(1,3),d3);	
		
		d1.setMin(0);
		d1.setMax(5);
		d3=IntegerInterval.union(d1, d2);
		assertEquals(d1,d3);	
	}

	@Test
	public void testAddIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.add(d1, d2);
		assertEquals(new IntegerInterval(3,10),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d3=IntegerInterval.add(d1, 3);
		assertEquals(new IntegerInterval(4,8),d3);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.add(d1, 3);
		assertEquals(new IntegerInterval(4,Long.MAX_VALUE),d3);	
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.add(d1, -3);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,-2),d3);	
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.add(d1, d2);
		assertEquals(new IntegerInterval(1,-2),d3);		
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.add(d2, d1);
		assertEquals(new IntegerInterval(1,-2),d3);				
	}

	@Test
	public void testSubIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.sub(d1, d2);
		assertEquals(new IntegerInterval(-4,3),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d3=IntegerInterval.sub(d1, 3);
		assertEquals(new IntegerInterval(-2,2),d3);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.sub(d1, 3);
		assertEquals(new IntegerInterval(-2,Long.MAX_VALUE),d3);	
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.sub(d1, -3);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,4),d3);	
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.sub(d1, d2);
		assertEquals(new IntegerInterval(1,-2),d3);		
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.sub(d2, d1);
		assertEquals(new IntegerInterval(1,-2),d3);			
	}

	@Test
	public void testMulIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(2,25),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d3=IntegerInterval.mul(d1, 3);
		assertEquals(new IntegerInterval(3,15),d3);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.mul(d1, 3);
		assertEquals(new IntegerInterval(3,Long.MAX_VALUE),d3);	
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.mul(d1, -3);
		assertEquals(new IntegerInterval(-3,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.mul(d1, 3);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,3),d3);
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(1,-2),d3);		
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.mul(d2, d1);
		assertEquals(new IntegerInterval(1,-2),d3);		
		
		//6*6种组合
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(1,100),d3);		
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);			
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);		
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,-1),d3);	
		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);			
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);			
		

		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);		
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);			
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);		
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);				
		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);			
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);			
				
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,-1),d3);		
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,0),d3);			
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(-100,100),d3);
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,100),d3);		
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.mul(d1, d2);
		assertEquals(new IntegerInterval(1,100),d3);			
	}

	@Test
	public void testDivIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=new IntegerInterval(2,5,false,false);
		IntegerInterval d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,2),d3);
		
		d1=new IntegerInterval(1,5,false,false);
		d3=IntegerInterval.div(d1, 2);
		assertEquals(new IntegerInterval(0,2),d3);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d3=IntegerInterval.div(d1, 2);
		assertEquals(new IntegerInterval(0,Long.MAX_VALUE),d3);	
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.div(d1, -2);
		assertEquals(new IntegerInterval(0,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d3=IntegerInterval.div(d1, 3);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,0),d3);
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(1,-2),d3);		
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		d3=IntegerInterval.div(d2, d1);
		assertEquals(new IntegerInterval(1,-2),d3);		
				
		//6*6种组合
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(1/10,10/1),d3);		
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(1/10,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,-1/10),d3);		
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MAX_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(1,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,-1/10),d3);	
		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,10/1),d3);		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,0),d3);		
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(0,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,0),d3);			
		

		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,10/1),d3);		
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);		
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);			
		
		d1=new IntegerInterval(-10,10,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,10/1),d3);				
		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-0,0),d3);
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);			
		
		d1=new IntegerInterval(0,0,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,0),d3);		
		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,0),d3);		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,0),d3);			
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,Long.MAX_VALUE),d3);		
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,0),d3);			
		
		d1=new IntegerInterval(-10,0,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(0,10/1),d3);			
				
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(1,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(-10/1,-1/10),d3);		
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(0,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,-1/10),d3);			
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,10,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MAX_VALUE),d3);
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(1/10,Long.MAX_VALUE),d3);		
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(0,0,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,Long.MIN_VALUE),d3);			
		
		d1=new IntegerInterval(-10,-1,false,false);
		d2=new IntegerInterval(-10,-1,false,false);
		d3=IntegerInterval.div(d1, d2);
		assertEquals(new IntegerInterval(1/10,10/1),d3);			
	}

	@Test
	public void testModIntegerIntervalIntegerInterval() {
		IntegerInterval d1=new IntegerInterval(1,5,false,false);
		IntegerInterval d2=IntegerInterval.uminus(d1);
		assertEquals(new IntegerInterval(-5,-1),d2);
		
		d1=new IntegerInterval(1,Long.MAX_VALUE,false,false);
		d2=IntegerInterval.uminus(d1);
		assertEquals(new IntegerInterval(Long.MIN_VALUE,-1),d2);	
		
		d1=new IntegerInterval(Long.MIN_VALUE,1,false,false);
		d2=IntegerInterval.uminus(d1);
		assertEquals(new IntegerInterval(-1,Long.MAX_VALUE),d2);
		
		d1=new IntegerInterval(5,1,false,false);
		d2=new IntegerInterval(1,1,false,false);
		IntegerInterval d3=IntegerInterval.mod(d2, d1);
		assertEquals(new IntegerInterval(1,-2),d3);		
	}

	@Test
	public void testUminus() {
		IntegerInterval d1=new IntegerInterval(5,5,false,false);
		IntegerInterval d2=IntegerInterval.mod(d1,2);
		assertEquals(new IntegerInterval(1,1),d2);
		
		d1=new IntegerInterval(10,10,false,false);
		d2=IntegerInterval.mod(d1,4);
		assertEquals(new IntegerInterval(2,2),d2);	
		
		d1=new IntegerInterval(10,10,false,false);
		d2=IntegerInterval.mod(d1,-4);
		assertEquals(new IntegerInterval(2,2),d2);
		
		d1=IntegerInterval.emptyInterval();
		d2=IntegerInterval.uminus(d1);
		assertEquals(IntegerInterval.emptyInterval(),d2);
	}

}
