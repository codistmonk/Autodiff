package autodiff.nodes;

import static autodiff.nodes.NodesTools.*;
import static java.lang.Math.min;

import java.io.Serializable;
import java.nio.FloatBuffer;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract interface Node<N extends Node<?>> extends Serializable {
	
	public abstract int[] getShape();
	
	public default boolean isComputationNode() {
		return true;
	}
	
	@SuppressWarnings("unchecked")
	public default N setShape(final int... shape) {
		checkLength(this.getLength(), product(shape));
		
		return (N) this;
	}
	
	public default <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public default boolean hasArguments() {
		return !this.getArguments().isEmpty();
	}
	
	public default Node<?> getArgumentAt(final int... indices) {
		Node<?> result = this;
		
		for (final int i : indices) {
			result = result.getArguments().get(i);
		}
		
		return result;
	}
	
	public abstract List<Node<?>> getArguments();
	
	public abstract FloatBuffer getFloatBuffer();
	
	public abstract void setupDiffs(boolean setupDiffs);
	
	public default boolean setupDiffs() {
		if (this.hasArguments()) {
			boolean needSetup = false;
			
			for (final Node<?> argument : this.getArguments()) {
				needSetup |= argument.setupDiffs();
			}
			
			this.setupDiffs(needSetup);
		}
		
		return this.getDiffs() != null;
	}
	
	public default boolean hasDiffs() {
		return this.getDiffs() != null;
	}
	
	public abstract Node<?> getDiffs();
	
	@SuppressWarnings("unchecked")
	public default N autoShape() {
		return (N) this;
	}
	
	public default int[] getLengths(final int[] result) {
		final int requestedDimensions = result.length;
		final int[] shape = this.getShape();
		final int naturalDimensions = shape.length;
		
		if (requestedDimensions == naturalDimensions) {
			System.arraycopy(shape, 0, result, 0, requestedDimensions);
		} else {
			Arrays.fill(result, 1);
			
			final int d = min(requestedDimensions, naturalDimensions);
			int i = 0;
			
			for (; i < d; ++i) {
				result[i] = shape[i];
			}
			
			for (; i < naturalDimensions; ++i) {
				result[requestedDimensions - 1] *= shape[i];
			}
		}
		
		return result;
	}
	
	public default int getLength() {
		return this.getLengths(new int[1])[0];
	}
	
	public default float get() {
		this.checkScalar();
		
		return this.get(0);
	}
	
	public default float[] get(final float[] result) {
		checkLength(this.getLength(), result.length);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().get(result);
		
		return result;
	}
	
	public default float get(final int index) {
		return this.getFloatBuffer().get(index);
	}
	
	@SuppressWarnings("unchecked")
	public default N set(final float... values) {
		final int n = values.length;
		
		if (this.getShape() == null) {
			this.setShape(n);
		}
		
		checkLength(this.getLength(), n);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().put(values);
		
		return (N) this;
	}
	
	@SuppressWarnings("unchecked")
	public default N set(final int index, final float value) {
		this.getFloatBuffer().put(index, value);
		
		return (N) this;
	}
	
	public default N add(final int index, final float value) {
		return this.set(index, this.get(index) + value);
	}
	
	public default <C extends Collection<Node<?>>> C collectTo(final C result) {
		// for ordered collections, make sure this is added after its dependents
		result.remove(this);
		result.add(this);
		
		this.getArguments().forEach(a -> a.collectTo(result));
		
		return result;
	}
	
	public default void checkScalar() {
		checkLength(1, this.getLength());
	}
	
}
