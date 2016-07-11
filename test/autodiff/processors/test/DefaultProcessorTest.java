package autodiff.processors.test;

import static org.junit.Assert.*;

import org.junit.Test;

import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.nodes.Selection;
import autodiff.processors.DefaultProcessor;
import autodiff.processors.NodeProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public class DefaultProcessorTest {
	
	@Test
	public final void test1() {
		final Node<?> x = new Data().setShape(2).set(42F, 33F);
		final Node<?> i = new Data().setShape(1).set(0F);
		final Node<?> xi = new Selection().setVectors(x).setIndices(i).autoShape();
		
		assertArrayEquals(new int[] { 2 }, x.getShape());
		assertArrayEquals(new int[] { 1 }, i.getShape());
		assertArrayEquals(new int[] { 1 }, xi.getShape());
		
		i.set(0F);
		
		this.getProcessor().fullForward(xi);
		
		assertEquals(42.0, xi.get(), 0.0);
		
		i.set(1F);
		
		this.getProcessor().fullForward(xi);
		
		assertEquals(33.0, xi.get(), 0.0);
	}
	
	public final NodeProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
}
