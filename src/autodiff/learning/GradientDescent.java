package autodiff.learning;

import java.util.BitSet;

import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public final class GradientDescent extends AbstractMinimizer {
	
	private int iterations;
	
	private float learningRate;
	
	private int currentIteration;
	
	public GradientDescent(final Node<?> cost) {
		super(cost);
		this.iterations = 10;
		this.learningRate = 0.1F;
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
	
	@Override
	public final void updateParameters() {
		this.getProcessor().fullBackwardDiff(this.getCost());
		
		final float s = -this.getLearningRate();
		
		for (final Node<?> p : this.getParameters()) {
			final BitSet locks = this.getParameterLocks().get(p);
			final int n = p.getLength();
			
			for (int i = 0; i < n; ++i) {
				if (locks == null || !locks.get(i)) {
					p.add(i, s * p.getDiffs().get(i));
				}
			}
		}
	}
	
	@Override
	public final void run() {
		this.getParameters().forEach(n -> n.setupDiffs(true));
		
		this.currentIteration = 0;
		
		super.run();
	}
	
	@Override
	public final boolean isDone() {
		return this.getIterations() <= ++this.currentIteration;
	}
	
	private static final long serialVersionUID = 463343929759033056L;
	
}
