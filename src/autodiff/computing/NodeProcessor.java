package autodiff.computing;

import static java.util.Collections.reverse;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;

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
	
	public default <N extends Node<?>> List<Node<?>> collectForward(final N node) {
		final List<Node<?>> result = new ArrayList<>(node.collectTo(new LinkedHashSet<>()));
		
		reverse(result);
		
		return result;
	}
	
	public default <N extends Node<?>> List<Node<?>> collectBackwardDiff(final N node) {
		final Collection<Node<?>> forwardNodes = node.collectTo(new LinkedHashSet<>());
		final LinkedHashSet<Node<?>> tmp = node.collectBackwardDiffNodesTo(new LinkedHashSet<>());
		
		tmp.removeAll(forwardNodes);
		
		final List<Node<?>> result = new ArrayList<>(tmp);
		
		reverse(result);
		
		return result;
	}
	
	public default void zeroComputationNodes(final Collection<Node<?>> nodes) {
		nodes.stream().filter(Node::isComputationNode).forEach(n -> this.fill(n, 0F));
	}
	
	public default <N extends Node<?>> N fullForward(final N node) {
		final List<Node<?>> nodes = collectForward(node);
		
		this.zeroComputationNodes(nodes);
		
		this.forward(nodes);
		
		return node;
	}
	
	public default <N extends Node<?>> N fullBackwardDiff(final N node) {
		if (node.setupDiffs()) {
			final List<Node<?>> nodes = collectBackwardDiff(node);
			
			this.zeroComputationNodes(nodes);
			
			this.fill(node.getDiffs(), 1F);
			
			this.forward(nodes);
		}
		
		return node;
	}
	
	public default void reset() {
		// NOP
	}
	
	public default void forward(final Iterable<Node<?>> nodes) {
		nodes.forEach(n -> n.accept(this.getForwarder()));
	}
	
}
