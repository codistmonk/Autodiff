package autodiff.learning.test;

import static autodiff.computing.Functions.SQUARED;
import static org.junit.Assert.*;

import java.util.Random;

import org.junit.Test;

import autodiff.learning.GradientDescent;
import autodiff.nodes.Data;
import autodiff.nodes.Mapping;
import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public final class GradientDescentTest {
	
	@Test
	public final void test1() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = new Mapping().setArgument(x).setFunctioName(SQUARED).autoShape();
		final GradientDescent gd = new GradientDescent(y).setIterations(50);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, y.get(), 1.0E-4);
	}
	
}
