package autodiff.learning;

import java.util.ArrayList;
import java.util.List;

import autodiff.computing.NodeProcessor;
import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public abstract class AbstractMinimizer implements Minimizer {
	
	private NodeProcessor processor;
	
	private final List<Node<?>> parameters;
	
	private final List<float[]> bestParameters;
	
	private final Node<?> cost;
	
	protected AbstractMinimizer(final Node<?> cost) {
		this.processor = Minimizer.super.getProcessor();
		this.parameters = new ArrayList<>();
		this.bestParameters = new ArrayList<>();
		this.cost = cost;
	}
	
	@Override
	public final NodeProcessor getProcessor() {
		return this.processor;
	}
	
	public final void setProcessor(final NodeProcessor processor) {
		this.processor = processor;
	}
	
	@Override
	public final List<Node<?>> getParameters() {
		return this.parameters;
	}
	
	@Override
	public final Node<?> getCost() {
		return this.cost;
	}
	
	@Override
	public final void saveBestParameters() {
		this.bestParameters.clear();
		
		this.getParameters().forEach(n -> this.bestParameters.add(n.get(new float[n.getLength()])));
	}
	
	@Override
	public final void restoreBestParameters() {
		final int n = this.bestParameters.size();
		
		for (int i = 0; i < n; ++i) {
			this.getParameters().get(i).set(this.bestParameters.get(i));
		}
	}
	
	private static final long serialVersionUID = 1301441706877706262L;
	
}
