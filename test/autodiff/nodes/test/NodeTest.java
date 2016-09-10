package autodiff.nodes.test;

import static org.junit.Assert.*;

import autodiff.computing.DefaultProcessor;
import autodiff.nodes.Computation;
import autodiff.nodes.Data;
import autodiff.nodes.Node;

import org.junit.Test;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class NodeTest {
	
	@Test
	public final void testShapes1() {
		final Node<?> x = new Data().setShape(1);
		
		assertArrayEquals(new int[] { 1 }, x.getShape());
		
		assertArrayEquals(new int[] { 1 }, x.getLengths(new int [1]));
		assertArrayEquals(new int[] { 1, 1 }, x.getLengths(new int [2]));
	}
	
	@Test
	public final void testShapes2() {
		final Node<?> x = new Data().setShape(2, 3, 4);
		
		assertArrayEquals(new int[] { 2, 3, 4 }, x.getShape());
		
		assertArrayEquals(new int[] { 24 }, x.getLengths(new int [1]));
		assertArrayEquals(new int[] { 2, 12 }, x.getLengths(new int [2]));
		assertArrayEquals(new int[] { 2, 3, 4 }, x.getLengths(new int [3]));
		assertArrayEquals(new int[] { 2, 3, 4, 1 }, x.getLengths(new int [4]));
	}
	
	@Test
	public final void testGetSet1() {
		final Node<?> x = new Data().setShape(1);
		
		x.set(42F);
		
		assertEquals(42.0, x.get(), 0.0);
	}
	
	@Test
	public final void testGetSet2() {
		final Node<?> x = new Data().setShape(2);
		
		x.set(42F, 33F);
		
		assertEquals(42.0, x.get(0), 0.0);
		assertEquals(33.0, x.get(1), 0.0);
	}
	
	@Test
	public final void testComputation1() {
		final Computation node = Computation.ones();
		
		node.set("shape", new int[] { 2 });
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 2 }, node.getShape());
		
		DefaultProcessor.INSTANCE.fullForward(node);
		
		assertArrayEquals(new float[] { 1F, 1F }, node.get(new float[node.getLength()]), 0F);
	}
	
	@Test
	public final void testComputation2() {
		final Computation node = Computation.ones();
		
		node.set("shape", new int[] { 2, 1, 3 });
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 2, 1, 3 }, node.getShape());
		
		DefaultProcessor.INSTANCE.fullForward(node);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F, 1F, 1F, 1F }, node.get(new float[node.getLength()]), 0F);
	}
	
	@Test
	public final void testComputation3() {
		final Computation node = Computation.range();
		
		node.set("n", 3);
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 3 }, node.getShape());
		
		DefaultProcessor.INSTANCE.fullForward(node);
		
		assertArrayEquals(new float[] { 0F, 1F, 2F }, node.get(new float[node.getLength()]), 0F);
	}
	
	@Test
	public final void testComputation4() {
		final Computation node = Computation.repeatAndIncrease();
		
		node.set("n", 3);
		node.set("stride", 2);
		node.set("delta", 5);
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 6 }, node.getShape());
		
		DefaultProcessor.INSTANCE.fullForward(node);
		
		assertArrayEquals(new float[] { 0F, 0F, 5F, 5F, 10F, 10F }, node.get(new float[node.getLength()]), 0F);
	}
	
}
