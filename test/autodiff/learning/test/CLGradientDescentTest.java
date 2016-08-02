package autodiff.learning.test;

import autodiff.computing.CLProcessor;

/**
 * @author codistmonk (creation 2016-08-02)
 */
public final class CLGradientDescentTest extends GradientDescentTest {
	
	@Override
	public final CLProcessor getProcessor() {
		return CLProcessor.INSTANCE;
	}
	
}
