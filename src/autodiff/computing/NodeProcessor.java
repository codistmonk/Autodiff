package autodiff.computing;

import java.io.Serializable;

import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract interface NodeProcessor extends Serializable {
	
	public abstract NodeVisitor<Void> getForwarder();
	
	public default <N extends Node<?>> N fill(final N node, final float value) {
		final int n = node.getLength();
		
		for (int i = 0; i < n; ++i) {
			node.set(i, value);
		}
		
		return node;
	}
	
	public abstract <N extends Node<?>> N fullForward(N node);
	
	public abstract <N extends Node<?>> N fullBackwardDiff(N node);
	
	public default void reset() {
		// NOP
	}
	
}
