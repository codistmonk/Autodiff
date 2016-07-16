package autodiff.learning;

import java.io.Serializable;
import java.util.BitSet;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import autodiff.computing.DefaultProcessor;
import autodiff.computing.NodeProcessor;
import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public abstract interface Minimizer<M extends Minimizer<?>> extends Runnable, Serializable {
	
	public default NodeProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
	public default Map<Node<?>, BitSet> getParameterLocks() {
		return Collections.emptyMap();
	}
	
	public abstract boolean isSavingBestParameters();
	
	public abstract M setSavingBestParameters(boolean savingBestParameters);
	
	@SuppressWarnings("unchecked")
	public default M setParameters(final Node<?>... parameters) {
		this.getParameters().clear();
		this.getParameterLocks().clear();
		
		for (final Node<?> n : parameters) {
			this.getParameters().add(n);
		}
		
		return (M) this;
	}
	
	public abstract List<Node<?>> getParameters();
	
	public abstract Node<?> getCost();
	
	public default void updateParameters() {
		// NOP
	}
	
	@Override
	public default void run() {
		float bestCost = updateCost(Float.POSITIVE_INFINITY);
		
		while (!this.isDone()) {
			this.updateParameters();
			
			bestCost = this.updateCost(bestCost);
		}
		
		this.restoreBestParameters();
	}
	
	public default float updateCost(final float previousBestCost) {
		this.getProcessor().fullForward(this.getCost());
		
		final float cost = this.getCost().get();
		
		if (cost < previousBestCost) {
			this.saveBestParameters();
			
			return cost;
		}
		
		return previousBestCost;
	}
	
	public default boolean isDone() {
		return true;
	}
	
	public default void saveBestParameters() {
		// NOP
	}
	
	public default void restoreBestParameters() {
		// NOP
	}
	
}
