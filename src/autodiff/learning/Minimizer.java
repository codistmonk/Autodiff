package autodiff.learning;

import java.io.Serializable;
import java.util.BitSet;
import java.util.Collection;
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
	
	public default Collection<Listener> getListeners() {
		return Collections.emptyList();
	}
	
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
		this.beforeUpdateParameters();
		this.afterUpdateParameters();
	}
	
	@Override
	public default void run() {
		this.beforeRun();
		
		float bestCost = updateCost(Float.POSITIVE_INFINITY);
		
		while (!this.isDone()) {
			this.updateParameters();
			
			bestCost = this.updateCost(bestCost);
		}
		
		this.restoreBestParameters();
		
		this.afterRun();
	}
	
	public default float updateCost(final float previousBestCost) {
		this.beforeUpdateCost();
		
		this.getProcessor().fullForward(this.getCost());
		
		final float cost = this.getCost().get();
		
		if (cost < previousBestCost) {
			this.saveBestParameters();
			
			this.afterUpdateCost();
			
			return cost;
		}
		
		this.afterUpdateCost();
		
		return previousBestCost;
	}
	
	public default boolean isDone() {
		return true;
	}
	
	public default void saveBestParameters() {
		if (this.isSavingBestParameters()) {
			this.beforeSaveBestParameters();
			this.afterSaveBestParameters();
		}
	}
	
	public default void restoreBestParameters() {
		if (this.isSavingBestParameters()) {
			this.beforeRestoreBestParameters();
			this.afterRestoreBestParameters();
		}
	}
	
	public default void beforeRun() {
		this.getListeners().forEach(Listener::beforeRun);
	}
	
	public default void afterRun() {
		this.getListeners().forEach(Listener::afterRun);
	}
	
	public default void beforeUpdateParameters() {
		this.getListeners().forEach(Listener::beforeUpdateParameters);
	}
	
	public default void afterUpdateParameters() {
		this.getListeners().forEach(Listener::afterUpdateParameters);
	}
	
	public default void beforeUpdateCost() {
		this.getListeners().forEach(Listener::beforeUpdateCost);
	}
	
	public default void afterUpdateCost() {
		this.getListeners().forEach(Listener::afterUpdateCost);
	}
	
	public default void beforeSaveBestParameters() {
		this.getListeners().forEach(Listener::beforeSaveBestParameters);
	}
	
	public default void afterSaveBestParameters() {
		this.getListeners().forEach(Listener::afterSaveBestParameters);
	}
	
	public default void beforeRestoreBestParameters() {
		this.getListeners().forEach(Listener::beforeRestoreBestParameters);
	}
	
	public default void afterRestoreBestParameters() {
		this.getListeners().forEach(Listener::afterRestoreBestParameters);
	}
	
	/**
	 * @author codistmonk (creation 2016-07-22)
	 */
	public static abstract interface Listener extends Serializable {
		
		public default void beforeRun() {
			// NOP
		}
		
		public default void afterRun() {
			// NOP
		}
		
		public default void beforeUpdateParameters() {
			// NOP
		}
		
		public default void afterUpdateParameters() {
			// NOP
		}
		
		public default void beforeUpdateCost() {
			// NOP
		}
		
		public default void afterUpdateCost() {
			// NOP
		}
		
		public default void beforeSaveBestParameters() {
			// NOP
		}
		
		public default void afterSaveBestParameters() {
			// NOP
		}
		
		public default void beforeRestoreBestParameters() {
			// NOP
		}
		
		public default void afterRestoreBestParameters() {
			// NOP
		}
		
	}
	
}
