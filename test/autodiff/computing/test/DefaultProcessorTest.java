package autodiff.computing.test;

import autodiff.computing.DefaultProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class DefaultProcessorTest extends ProcessorTest {
	
	@Override
	public final DefaultProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
}
