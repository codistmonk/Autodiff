package autodiff.computing;

import static java.util.Collections.reverse;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;

import autodiff.nodes.CustomNode;
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
//		final List<Node<?>> result = new ArrayList<>(node.collectTo(new LinkedHashSet<>()));
		final List<Node<?>> result = new ArrayList<>(node.accept(new ForwardCollector()));
		
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
	
	/**
	 * @author codistmonk (creation 2016-08-02)
	 */
	public static final class ForwardCollector implements NodeVisitor<Collection<Node<?>>> {
		
		private final Collection<Node<?>> result = new LinkedHashSet<>();
		
		@Override
		public final Collection<Node<?>> visit(final Node<?> node) {
			// for ordered collections, make sure this is added after its dependents
			this.result.remove(node);
			this.result.add(node);
			
			node.getArguments().forEach(a -> a.accept(this));
			node.getAdditionalDependencies().forEach(a -> a.accept(this));
			
			return this.result;
		}
		
		@Override
		public final Collection<Node<?>> visit(final CustomNode node) {
			return node.unfold().accept(this);
		}
		
		private static final long serialVersionUID = 7381617866288668668L;
		
	}
	
}
