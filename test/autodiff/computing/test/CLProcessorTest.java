package autodiff.computing.test;

import org.junit.Ignore;

import autodiff.computing.CLProcessor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
@Ignore
public final class CLProcessorTest extends ProcessorTest {
	
	@Override
	public final CLProcessor getProcessor() {
		return CLProcessor.INSTANCE;
	}
	
}
