package autodiff.learning.test;

import static autodiff.computing.Functions.COS;
import static autodiff.computing.Functions.SQUARED;
import static autodiff.computing.Functions.TIMES;
import static autodiff.nodes.NodesTools.$;
import static org.junit.Assert.*;

import java.util.Random;

import org.junit.Test;

import autodiff.learning.GradientDescent;
import autodiff.nodes.Data;
import autodiff.nodes.Node;

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
	
}
