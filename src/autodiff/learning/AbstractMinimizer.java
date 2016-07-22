package autodiff.learning;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import autodiff.computing.NodeProcessor;
import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public abstract class AbstractMinimizer<M extends AbstractMinimizer<?>> implements Minimizer<M> {
	
	private final Collection<Listener> listeners;
	
	private NodeProcessor processor;
	
	private final List<Node<?>> parameters;
	
	private final Map<Node<?>, BitSet> parameterLocks;
	
	private final List<float[]> bestParameters;
	
	private final Node<?> cost;
	
	private boolean savingBestParameters;
	
	protected AbstractMinimizer(final Node<?> cost) {
		this.listeners = new ArrayList<>();
		this.processor = Minimizer.super.getProcessor();
		this.parameters = new ArrayList<>();
		this.parameterLocks = new HashMap<>();
		this.bestParameters = new ArrayList<>();
		this.cost = cost;
		this.savingBestParameters = true;
	}
	
	@Override
	public final Collection<Listener> getListeners() {
		return this.listeners;
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
	public final Map<Node<?>, BitSet> getParameterLocks() {
		return this.parameterLocks;
	}
	
	@Override
	public final Node<?> getCost() {
		return this.cost;
	}
	
	@Override
	public final boolean isSavingBestParameters() {
		return this.savingBestParameters;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public final M setSavingBestParameters(final boolean savingBestParameters) {
		this.savingBestParameters = savingBestParameters;
		
		return (M) this;
	}
	
	@Override
	public final void saveBestParameters() {
		if (this.isSavingBestParameters()) {
			this.beforeSaveBestParameters();
			
			this.bestParameters.clear();
			
			this.getParameters().forEach(n -> this.bestParameters.add(n.get(new float[n.getLength()])));
			
			this.afterSaveBestParameters();
		}
	}
	
	@Override
	public final void restoreBestParameters() {
		if (this.isSavingBestParameters()) {
			this.beforeRestoreBestParameters();
			
			final int n = this.bestParameters.size();
			
			for (int i = 0; i < n; ++i) {
				this.getParameters().get(i).set(this.bestParameters.get(i));
			}
			
			this.getProcessor().fullForward(this.getCost());
			
			this.afterRestoreBestParameters();
		}
	}
	
	private static final long serialVersionUID = 1301441706877706262L;
	
}
