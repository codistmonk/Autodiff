package autodiff.processors.test;

import static java.lang.Math.exp;
import static org.junit.Assert.*;

import org.junit.Test;

import autodiff.nodes.Convolution2D;
import autodiff.nodes.Data;
import autodiff.nodes.Functions;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node;
import autodiff.nodes.Selection;
import autodiff.nodes.Sum;
import autodiff.nodes.Zipping;
import autodiff.processors.DefaultProcessor;
import autodiff.processors.NodeProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class DefaultProcessorTest {
	
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
		
		x.setupDiffs(true);
		
		assertArrayEquals(x.getShape(), x.getDiffs().getShape());
		
		this.getProcessor().fullBackwardDiff(xi);
		
		assertArrayEquals(new float[] { 0F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
		
		i.set(0F);
		
		this.getProcessor().fullBackwardDiff(xi);
		
		assertArrayEquals(new float[] { 1F, 0F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testMatrixMultiplication1() {
		final Node<?> a = new Data().setShape(1, 2).set(
				2F, 3F);
		final Node<?> b = new Data().setShape(2, 1).set(
				4F,
				5F);
		final Node<?> c = new MatrixMultiplication().setLeft(a).setRight(b).autoShape();
		
		assertArrayEquals(new int[] { 1, 1 }, c.getShape());
		
		this.getProcessor().fullForward(c);
		
		assertArrayEquals(new float[] {
				23F
		}, c.get(new float[c.getLength()]), 0F);
		
		a.setupDiffs(true);
		b.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(c);
		
		assertArrayEquals(new float[] {
				4F, 5F
		}, a.getDiffs().get(new float[a.getLength()]), 0F);
		
		assertArrayEquals(new float[] {
				2F, 3F
		}, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	@Test
	public final void testMatrixMultiplication2() {
		final Node<?> a = new Data().setShape(1, 2).set(
				2F, 3F);
		final Node<?> b = new Data().setShape(2, 1).set(
				4F,
				5F);
		final Node<?> c = new MatrixMultiplication().setLeft(b).setRight(a).autoShape();
		
		assertArrayEquals(new int[] { 2, 2 }, c.getShape());
		
		this.getProcessor().fullForward(c);
		
		assertArrayEquals(new float[] {
				8F, 12F,
				10F, 15F
		}, c.get(new float[c.getLength()]), 0F);
		
		a.setupDiffs(true);
		b.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(c);
		
		assertArrayEquals(new float[] {
				9F, 9F
		}, a.getDiffs().get(new float[a.getLength()]), 0F);
		
		assertArrayEquals(new float[] {
				5F, 5F
		}, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	@Test
	public final void testSum1() {
		final Node<?> x = new Data().setShape(1, 2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = new Sum().setArgument(x).autoShape();
		
		assertArrayEquals(new int[] { 1, 2 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 6F, 15F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testSum2() {
		final Node<?> x = new Data().setShape(1, 2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = new Sum().setArgument(x).setStride(6).autoShape();
		
		assertArrayEquals(new int[] { 1 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 21F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMaxPooling1() {
		final Node<?> x = new Data().setShape(1, 1, 3, 3).set(
				1F, 2F, 3F,
				4F, 5F, 6F,
				7F, 8F, 9F);
		final Node<?> y = new MaxPooling2D().setArgument(x).setStrides(2).setKernelSide(2).autoShape();
		
		assertArrayEquals(new int[] { 1, 1, 2, 2 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] {
				5F, 6F,
				8F, 9F
		}, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMaxPooling2() {
		final Node<?> x = new Data().setShape(1, 2, 3, 3).set(
				1F, 2F, 3F,
				4F, 5F, 6F,
				7F, 8F, 9F,
				10F, 11F, 12F,
				13F, 14F, 15F,
				16F, 17F, 18F);
		final Node<?> y = new MaxPooling2D().setInputs(x).setOffsets(1).setStrides(2).setKernelSide(3).autoShape();
		
		assertArrayEquals(new int[] { 1, 2, 1, 1 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] {
				9F,
				18F
		}, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testConvolution1() {
		final Node<?> inputs = new Data().setShape(1, 1, 3, 3).set(
				1F, 2F, 3F,
				4F, 5F, 6F,
				7F, 8F, 9F);
		final Node<?> kernel = new Data().setShape(2, 2).set(
				1F, 2F,
				3F, 4F);
		final Node<?> y = new Convolution2D().setInputs(inputs).setKernel(kernel).setStrides(2).autoShape();
		
		assertArrayEquals(new int[] { 1, 1, 2, 2 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] {
				37F, 21F,
				23F, 9F
		}, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(Functions.ID).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { -1F, 0F, 1F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping2() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(Functions.SQUARED).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 1F, 0F, 1F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping3() {
		final Node<?> x = new Data().set(0F, 1F, 4F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(Functions.SQRT).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 0F, 1F, 2F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping4() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(Functions.SIGMOID).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { sigmoid(-1F), sigmoid(0F), sigmoid(1F) }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping5() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(Functions.STEP).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 0F, 1F, 1F }, y.get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testZipping1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Data().set(-1F, 0F, 1F);
		final Node<?> z = new Zipping().setLeft(x).setRight(y).setFunctionName("+").autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(z);
		
		assertArrayEquals(new float[] { -2F, 0F, 2F }, z.get(new float[z.getLength()]), 0F);
	}
	
	@Test
	public final void testNet1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> a = new Data().set(2F);
		final Node<?> b = new Data().set(3F);
		final Node<?> ax = new Zipping().setLeft(x).setRight(a).setFunctionName(Functions.TIMES).autoShape();
		final Node<?> z = new Zipping().setLeft(ax).setRight(b).setFunctionName("+").autoShape();
		
		this.getProcessor().fullForward(z);
		
		assertArrayEquals(new float[] { 1F, 3F, 5F }, z.get(new float[z.getLength()]), 0F);
	}
	
	public final NodeProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
	public static final float sigmoid(final float x) {
		return 1F / (1F + (float) exp(-x));
	}
	
}
