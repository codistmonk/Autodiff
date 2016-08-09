package autodiff.learning;

import autodiff.io.LabeledData;

/**
 * @author codistmonk (creation 2016-07-16)
 */
public final class MinibatchMinimizer extends AbstractMinimizer<MinibatchMinimizer> {
	
	private final Minimizer<?> iterationMinimizer;
	
	private final MinibatchContext minibatchContext;
	
	private int epochs;
	
	private int currentEpoch;
	
	public MinibatchMinimizer(final Minimizer<?> iterationMinimizer, final LabeledData trainingData, final LabeledData minibatchData) {
		super(iterationMinimizer.getCost());
		this.iterationMinimizer = iterationMinimizer;
		this.minibatchContext = new MinibatchContext(trainingData, minibatchData);
		this.epochs = 10;
		
		this.setProcessor(iterationMinimizer.getProcessor());
		
		iterationMinimizer.setSavingBestParameters(false);
	}
	
	public final Minimizer<?> getIterationMinimizer() {
		return this.iterationMinimizer;
	}
	
	public final MinibatchContext getMinibatchContext() {
		return this.minibatchContext;
	}
	
	public final int getEpochs() {
		return this.epochs;
	}
	
	public final int getCurrentEpoch() {
		return this.currentEpoch;
	}
	
	public final MinibatchMinimizer setEpochs(final int epochs) {
		this.epochs = epochs;
		
		return this;
	}
	
	@Override
	public final void run() {
		this.getParameters().clear();
		this.getParameters().addAll(this.getIterationMinimizer().getParameters());
		this.getParameterLocks().clear();
		this.getParameterLocks().putAll(this.getIterationMinimizer().getParameterLocks());
		this.currentEpoch = 0;
		
		super.run();
	}
	
	@Override
	public final boolean isDone() {
		return this.getEpochs() <= ++this.currentEpoch;
	}
	
	@Override
	public final void updateParameters() {
		this.beforeUpdateParameters();
		this.getMinibatchContext().forEachMinibatch(this.getIterationMinimizer());
		this.afterUpdateParameters();
	}
	
	@Override
	public final float updateCost(final float previousBestCost) {
		this.beforeUpdateCost(previousBestCost);
		
		final float[] cost = { 0F };
		final int[] count = { 0 };
		
		this.getMinibatchContext().forEachMinibatch(() -> {
			cost[0] += this.getProcessor().fullForward(this.getCost()).get();
			++count[0];
		});
		
		if (0 < count[0]) {
			cost[0] /= count[0];
		}
		
		float result = previousBestCost;
		
		if (cost[0] < previousBestCost) {
			this.saveBestParameters();
			
			result = cost[0];
		}
		
		this.afterUpdateCost(cost[0], result);
		
		return result;
	}
	
	private static final long serialVersionUID = 1342716574795573640L;
	
}