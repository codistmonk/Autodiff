package autodiff.processors.test;

import static org.junit.Assert.*;

import org.junit.Test;

import autodiff.nodes.Data;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.Selection;
import autodiff.processors.DefaultProcessor;
import autodiff.processors.NodeProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public class DefaultProcessorTest {
	
	@Test
	public final void testSelection1() {
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
	
	@Test
	public final void testMatrixMultiplication1() {
		final Node<?> a = new Data().setShape(1, 2).set(
				2F, 3F);
		final Node<?> b = new Data().setShape(2, 1).set(
				4F,
				5F);
		
		{
			final Node<?> c = new MatrixMultiplication().setLeft(a).setRight(b).autoShape();
			
			assertArrayEquals(new int[] { 1, 1 }, c.getShape());
			
			this.getProcessor().fullForward(c);
			
			assertArrayEquals(new float[] {
					23F
			}, c.get(new float[c.getLength()]), 0F);
		}
		
		{
			final Node<?> c = new MatrixMultiplication().setLeft(b).setRight(a).autoShape();
			
			assertArrayEquals(new int[] { 2, 2 }, c.getShape());
			
			this.getProcessor().fullForward(c);
			
			assertArrayEquals(new float[] {
					8F, 12F,
					10F, 15F
			}, c.get(new float[c.getLength()]), 0F);
		}
	}
	
	public final NodeProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
}
