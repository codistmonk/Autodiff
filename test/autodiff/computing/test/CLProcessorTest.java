package autodiff.computing.test;

import autodiff.computing.CLProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class CLProcessorTest extends ProcessorTest {
	
	@Override
	public final CLProcessor getProcessor() {
		return CLProcessor.INSTANCE;
	}
	
}
