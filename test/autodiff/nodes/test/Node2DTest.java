package autodiff.nodes.test;

import static org.junit.Assert.*;

import org.junit.Test;

import autodiff.nodes.Data;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node2D;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Node2DTest {
	
	@Test
	public final void testShapes1() {
		final Node2D<?> x = new MaxPooling2D().setArgument(new Data().setShape(1, 4, 4)).setOffsetX(1).setStrideX(2).autoShape();
		
		assertArrayEquals(new int[] { 1, 4, 2 }, x.getShape());
	}
	
}
