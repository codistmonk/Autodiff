package autodiff.learning.test;

import autodiff.computing.CLProcessor;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class CLMNISTTest extends MNISTTest {
	
	@Override
	public final CLProcessor getProcessor() {
		return CLProcessor.INSTANCE;
	}

}
