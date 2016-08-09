package autodiff.learning.test;

import autodiff.computing.DefaultProcessor;

/**
 * @author codistmonk (creation 2016-08-08)
 */
public final class DefaultMNISTTest extends MNISTTest {
	
	@Override
	public final DefaultProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}

}
