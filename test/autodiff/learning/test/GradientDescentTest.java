package autodiff.learning.test;

import static autodiff.computing.Functions.COS;
import static autodiff.computing.Functions.SQMINUS;
import static autodiff.computing.Functions.SQUARED;
import static autodiff.computing.Functions.SUM;
import static autodiff.computing.Functions.TIMES;
import static autodiff.nodes.NodesTools.$;
import static org.junit.Assert.*;

import autodiff.io.Iris;
import autodiff.io.LabeledData;
import autodiff.learning.GradientDescent;
import autodiff.nodes.Data;
import autodiff.nodes.Node;

import java.util.Random;

import org.junit.Test;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public final class GradientDescentTest {
	
	@Test
	public final void test1() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $(x, SQUARED);
		final GradientDescent gd = new GradientDescent(y).setIterations(100);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, x.get(), 1.0E-4);
		assertEquals(0.0, y.get(), 1.0E-4);
	}
	
	@Test
	public final void test2() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $($(x, SQUARED), "-", $(COS, $(8, TIMES, x)));
		final GradientDescent gd = new GradientDescent(y).setIterations(50).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, x.get(), 1.0E-4);
		assertEquals(-1.0, y.get(), 1.0E-4);
	}
	
	@Test
	public final void test3() {
		final Random random = new Random(2L);
		final Node<?> m = new Data().setShape(2, 2).set(
				1F, 2F,
				2F, 1F);
		final Node<?> v = new Data().setShape(2, 2).set(
				random.nextFloat(), random.nextFloat(),
				random.nextFloat(), random.nextFloat());
		final Node<?> k = new Data().setShape(1, 2).set(
				random.nextFloat(), random.nextFloat());
		final Node<?> mv = $(m, v);
		final Node<?> vk = $(v, ".*", k);
		final Node<?> vSquared = $(v, SQUARED);
		final Node<?> v2 = $(SUM, new int[] { 2, 1 }, vSquared);
		final Node<?> lengthConstraint = $(SUM, $(v2, SQMINUS, $(1F, 1F)));
		final Node<?> colinearityConstraint = $(SUM, $(mv, SQMINUS, vk));
		final Node<?> orthogonalityConstraint = $($($(v, "@", $(0, 0)).setShape(1, 2), $(v, "@", $(1, 1)).setShape(2, 1)), SQUARED);
		final Node<?> w = $(1, 1, 1.63);
		final Node<?> z = $($($(w, "@", 0), ".*", colinearityConstraint), "+", $($($(w, "@", 1), ".*", orthogonalityConstraint), "+", $($(w, "@", 2), ".*", lengthConstraint)));
		final GradientDescent gd = new GradientDescent(z).setIterations(200).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
		gd.getParameters().add(v);
		gd.getParameters().add(k);
		gd.run();
		
		Tools.debugPrint(m);
		Tools.debugPrint(v);
		Tools.debugPrint(k);
		Tools.debugPrint(z);
		Tools.debugPrint(colinearityConstraint, orthogonalityConstraint, lengthConstraint);
		
		assertArrayEquals(new float[] { 3F, -1F }, k.get(new float[k.getLength()]), 1E-4F);
		assertEquals(0.0, z.get(), 1.0E-4);
	}
	
	@Test
	public final void testIris1() {
		final Random random = new Random(2L);
		final LabeledData allData = Iris.getIrisData();
		
		allData.shuffle(random);
		
		final LabeledData[] trainTest = allData.split(2.0 / 3.0);
		
		fail("TODO");
	}
	
}
