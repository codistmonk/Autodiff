package autodiff.learning;

import autodiff.nodes.Node;

import java.util.BitSet;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public final class GradientDescent extends AbstractMinimizer<GradientDescent> {
	
	private int iterations;
	
	private float learningRate;
	
	private int currentIteration;
	
	private float currentLearningRate;
	
	private float learningRateDivisor;
	
	private float learningRateMultiplier;
	
	private float previousCost;
	
	public GradientDescent(final Node<?> cost) {
		super(cost);
		this.iterations = 10;
		this.learningRate = 0.1F;
		this.learningRateDivisor = 1F;
		this.learningRateMultiplier = 1F;
	}
	
	public final float getLearningRateDivisor() {
		return this.learningRateDivisor;
	}
	
	public final GradientDescent setLearningRateDivisor(final float learningRateDivisor) {
		this.learningRateDivisor = learningRateDivisor;
		
		return this;
	}
	
	public final float getLearningRateMultiplier() {
		return this.learningRateMultiplier;
	}
	
	public final GradientDescent setLearningRateMultiplier(final float learningRateMultiplier) {
		this.learningRateMultiplier = learningRateMultiplier;
		
		return this;
	}

	public final int getIterations() {
		return this.iterations;
	}
	
	public final GradientDescent setIterations(final int iterations) {
		this.iterations = iterations;
		
		return this;
	}
	
	public final float getLearningRate() {
		return this.learningRate;
	}
	
	public final GradientDescent setLearningRate(final float learningRate) {
		this.learningRate = learningRate;
		
		return this;
	}
	
	public final int getCurrentIteration() {
		return this.currentIteration;
	}
	
	public final float getCurrentLearningRate() {
		return this.currentLearningRate;
	}
	
	@Override
	public final void updateParameters() {
		this.beforeUpdateParameters();
		
		if (isCostInvalid(this.getCost().get())) {
			this.restoreBestParameters();
			this.currentLearningRate /= this.getLearningRateDivisor();
		}
		
		this.getProcessor().fullBackwardDiff(this.getCost());
		
		{
			final float cost = this.getCost().get();
			
			if (!Float.isNaN(this.previousCost)) {
				if (this.previousCost < cost) {
					this.currentLearningRate /= this.getLearningRateDivisor();
				} else {
					this.currentLearningRate *= this.getLearningRateMultiplier();
				}
			}
			
			this.previousCost = cost;
		}
		
		final float s = -this.getCurrentLearningRate();
		
		for (final Node<?> p : this.getParameters()) {
			final BitSet locks = this.getParameterLocks().get(p);
			final int n = p.getLength();
			
			for (int i = 0; i < n; ++i) {
				if (locks == null || !locks.get(i)) {
					p.add(i, s * p.getDiffs().get(i));
				}
			}
		}
		
		this.afterUpdateParameters();
	}
	
	@Override
	public final void run() {
		this.getParameters().forEach(n -> n.setupDiffs(true));
		
		this.currentIteration = 0;
		this.currentLearningRate = this.getLearningRate();
		this.previousCost = Float.NaN;
		
		super.run();
	}
	
	@Override
	public final boolean isDone() {
		return this.getIterations() < ++this.currentIteration;
	}
	
	private static final long serialVersionUID = 463343929759033056L;
	
	public static final boolean isCostInvalid(final float cost) {
		return Float.isNaN(cost) || (0 < cost && Float.isInfinite(cost));
	}
	
}
