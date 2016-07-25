package autodiff.computing.test;

import static autodiff.computing.Functions.EPSILON;
import static autodiff.nodes.NodesTools.sum;
import static java.lang.Math.exp;
import static org.junit.Assert.*;
import autodiff.computing.Functions;
import autodiff.computing.NodeProcessor;
import autodiff.nodes.Convolution2D;
import autodiff.nodes.Data;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node;
import autodiff.nodes.Selection;
import autodiff.nodes.Zipping;

import org.junit.After;
import org.junit.Test;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class ProcessorTest {
	
	protected ProcessorTest() {
		// NOP
	}
	
	@Test
	public final void testSelection1() {
		final Node<?> x = new Data().set(42F, 33F);
		final Node<?> i = new Data().set(0F);
		final Node<?> xi = new Selection().setVectors(x).setIndices(i).autoShape();
		
		assertArrayEquals(new int[] { 2 }, x.getShape());
		assertArrayEquals(new int[] { 1 }, i.getShape());
		assertArrayEquals(new int[] { 1, 1 }, xi.getShape());
		
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
	public final void testSelection2() {
		final Node<?> x = new Data().setShape(2, 2).set(
				1F, 2F,
				3F, 4F);
		final Node<?> i = new Data().set(
				1F, 1F, 0F);
		final Node<?> xi = new Selection().setVectors(x).setIndices(i).autoShape();
		
		assertArrayEquals(new int[] { 2, 2 }, x.getShape());
		assertArrayEquals(new int[] { 3 }, i.getShape());
		assertArrayEquals(new int[] { 2, 3 }, xi.getShape());
		
		this.getProcessor().fullForward(xi);
		
		assertArrayEquals(new float[] {
				2F, 2F, 1F,
				4F, 4F, 3F
		}, xi.get(new float[xi.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(xi);
		
		assertArrayEquals(new float[] {
				1F, 2F,
				1F, 2F
		}, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testSelection3() {
		final Node<?> x = new Data().setShape(2, 2).set(
				1F, 2F,
				3F, 4F);
		final Node<?> i = new Data().setShape(2, 1).set(
				0F, 0F);
		final Node<?> xi = new Selection().setVectors(x).setIndices(i).autoShape();
		
		assertArrayEquals(new int[] { 2, 2 }, x.getShape());
		assertArrayEquals(new int[] { 2, 1 }, i.getShape());
		assertArrayEquals(new int[] { 2, 1 }, xi.getShape());
		
		this.getProcessor().fullForward(xi);
		
		assertArrayEquals(new float[] {
				1F,
				3F
		}, xi.get(new float[xi.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(xi);
		
		assertArrayEquals(new float[] {
				1F, 0F,
				1F, 0F
		}, x.getDiffs().get(new float[x.getLength()]), 0F);
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
				2F,
				3F
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
				5F,
				5F
		}, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	@Test
	public final void testMatrixMultiplication3() {
		final Node<?> a = new Data().setShape(3, 2).set(
				2F, 3F,
				4F, 5F,
				6F, 7F);
		final Node<?> b = new Data().setShape(3, 1).set(
				8F,
				9F,
				10F);
		final Node<?> c = new MatrixMultiplication().setLeft(a).setTransposeLeft(true).setRight(b).autoShape();
		
		assertArrayEquals(new int[] { 2, 1 }, c.getShape());
		
		this.getProcessor().fullForward(c);
		
		assertArrayEquals(new float[] {
				112F, 139F
		}, c.get(new float[c.getLength()]), 0F);
		
		a.setupDiffs(true);
		b.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(c);
		
		assertArrayEquals(new float[] {
				8F, 8F,
				9F, 9F,
				10F, 10F
		}, a.getDiffs().get(new float[a.getLength()]), 0F);
		
		assertArrayEquals(new float[] {
				5F,
				9F,
				13F
		}, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	@Test
	public final void testMatrixMultiplication4() {
		final Node<?> a = new Data().setShape(2, 1).set(
				8F,
				9F);
		final Node<?> b = new Data().setShape(3, 2).set(
				2F, 3F,
				4F, 5F,
				6F, 7F);
		final Node<?> c = new MatrixMultiplication().setLeft(a).setTransposeLeft(true).setRight(b).setTransposeRight(true).autoShape();
		
		assertArrayEquals(new int[] { 1, 3 }, c.getShape());
		
		this.getProcessor().fullForward(c);
		
		assertArrayEquals(new float[] {
				43F, 77F, 111F
		}, c.get(new float[c.getLength()]), 0F);
		
		a.setupDiffs(true);
		b.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(c);
		
		assertArrayEquals(new float[] {
				12F,
				15F,
		}, a.getDiffs().get(new float[a.getLength()]), 0F);
		
		assertArrayEquals(new float[] {
				8F, 9F,
				8F, 9F,
				8F, 9F
		}, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	@Test
	public final void testSum1() {
		final Node<?> x = new Data().setShape(1, 2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = sum(x, 1, 1, 3);
		
		assertArrayEquals(new int[] { 1, 2, 1 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 6F, 15F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F, 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testSum2() {
		final Node<?> x = new Data().setShape(2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = sum(x, 2, 1);
		
		assertArrayEquals(new int[] { 1, 3 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 5F, 7F, 9F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F, 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testSum3() {
		final Node<?> x = new Data().setShape(2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = sum(x, 3);
		
		assertArrayEquals(new int[] { 2 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 6F, 15F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F, 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testSum4() {
		final Node<?> x = new Data().setShape(1, 2, 3).set(1F, 2F, 3F, 4F, 5F, 6F);
		final Node<?> y = sum(x);
		
		assertArrayEquals(new int[] { 1 }, y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 21F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F, 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
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
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] {
				0F, 0F, 0F,
				0F, 1F, 1F,
				0F, 1F, 1F
		}, x.getDiffs().get(new float[x.getLength()]), 0F);
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
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] {
				0F, 0F, 0F,
				0F, 0F, 0F,
				0F, 0F, 1F,
				
				0F, 0F, 0F,
				0F, 0F, 0F,
				0F, 0F, 1F
		}, x.getDiffs().get(new float[x.getLength()]), 0F);
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
		
		inputs.setupDiffs(true);
		kernel.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] {
				1F, 2F, 1F,
				3F, 4F, 3F,
				1F, 2F, 1F
		}, inputs.getDiffs().get(new float[inputs.getLength()]), 0F);
		
		assertArrayEquals(new float[] {
				20F, 10F,
				10F, 5F
		}, kernel.getDiffs().get(new float[kernel.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctionName(Functions.ID).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { -1F, 0F, 1F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping2() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctionName(Functions.SQUARED).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 1F, 0F, 1F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { -2F, 0F, 2F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping3() {
		final Node<?> x = new Data().set(0F, 1F, 4F);
		final Node<?> y = new Mapping().setArgument(x).setFunctionName(Functions.SQRT).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 0F, 1F, 2F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { Float.POSITIVE_INFINITY, 0.5F, 0.25F }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping4() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctionName(Functions.SIGMOID).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { sigmoid(-1F), sigmoid(0F), sigmoid(1F) }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { sigmoidDiff(-1F), sigmoidDiff(0F), sigmoidDiff(1F) }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testMapping5() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Mapping().setArgument(x).setFunctionName(Functions.STEP).autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(y);
		
		assertArrayEquals(new float[] { 0F, 1F, 1F }, y.get(new float[y.getLength()]), 0F);
		
		x.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(y);
		
		assertArrayEquals(new float[] { (float) EPSILON, (float) EPSILON, (float) EPSILON }, x.getDiffs().get(new float[x.getLength()]), 0F);
	}
	
	@Test
	public final void testZipping1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> y = new Data().set(-1F, 0F, 1F);
		final Node<?> z = new Zipping().setLeft(x).setRight(y).setFunctionName("+").autoShape();
		
		assertArrayEquals(x.getShape(), y.getShape());
		
		this.getProcessor().fullForward(z);
		
		assertArrayEquals(new float[] { -2F, 0F, 2F }, z.get(new float[z.getLength()]), 0F);
		
		x.setupDiffs(true);
		y.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(z);
		
		assertArrayEquals(new float[] { 1F, 1F, 1F }, x.getDiffs().get(new float[x.getLength()]), 0F);
		assertArrayEquals(new float[] { 1F, 1F, 1F }, y.getDiffs().get(new float[y.getLength()]), 0F);
	}
	
	@Test
	public final void testNet1() {
		final Node<?> x = new Data().set(-1F, 0F, 1F);
		final Node<?> a = new Data().set(2F);
		final Node<?> b = new Data().set(3F);
		final Node<?> ax = new Zipping().setLeft(x).setRight(a).setFunctionName("*").autoShape();
		final Node<?> z = new Zipping().setLeft(ax).setRight(b).setFunctionName("+").autoShape();
		
		this.getProcessor().fullForward(z);
		
		assertArrayEquals(new float[] { 1F, 3F, 5F }, z.get(new float[z.getLength()]), 0F);
		
		x.setupDiffs(true);
		a.setupDiffs(true);
		b.setupDiffs(true);
		
		this.getProcessor().fullBackwardDiff(z);
		
		assertArrayEquals(new float[] { 2F, 2F, 2F }, x.getDiffs().get(new float[x.getLength()]), 0F);
		assertArrayEquals(new float[] { 0F }, a.getDiffs().get(new float[a.getLength()]), 0F);
		assertArrayEquals(new float[] { 3F }, b.getDiffs().get(new float[b.getLength()]), 0F);
	}
	
	public abstract NodeProcessor getProcessor();
	
	@After
	public final void afterEachTest() {
		this.getProcessor().reset();
	}
	
	public static final float sigmoid(final float x) {
		return 1F / (1F + (float) exp(-x));
	}
	
	public static final float sigmoidDiff(final float x) {
		final float y = sigmoid(x);
		
		return y * (1F - y);
	}
	
}
