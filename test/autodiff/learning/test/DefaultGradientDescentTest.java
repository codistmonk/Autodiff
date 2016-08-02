package autodiff.learning.test;

import autodiff.computing.DefaultProcessor;

/**
 * @author codistmonk (creation 2016-08-02)
 */
public final class DefaultGradientDescentTest extends GradientDescentTest {
	
	@Override
	public final DefaultProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
}
