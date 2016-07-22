package autodiff.learning;

import static java.lang.Math.min;

import java.io.Serializable;

import autodiff.io.LabeledData;

/**
 * @author codistmonk (creation 2016-07-16)
 */
public final class MinibatchContext implements Serializable {
	
	private final LabeledData sourceData;
	
	private final LabeledData minibatchData;
	
	public MinibatchContext(final LabeledData sourceData, final LabeledData minibatchData) {
		this.sourceData = sourceData;
		this.minibatchData = minibatchData;
	}
	
	public final LabeledData getSourceData() {
		return this.sourceData;
	}
	
	public final LabeledData getMinibatchData() {
		return this.minibatchData;
	}
	
	public final void forEachMinibatch(final Runnable command) {
		final int m = this.getSourceData().getItemCount();
		final int n = this.getMinibatchData().getItemCount();
		
		for (int i = 0; i < m; i += n) {
			this.getSourceData().copy(i, min(i + n, m - i), this.getMinibatchData(), 0);
			command.run();
		}
	}
	
	private static final long serialVersionUID = -4327393127426597114L;
	
}