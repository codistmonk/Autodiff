package autodiff.computing;

import static java.util.Collections.reverse;

import autodiff.nodes.CustomNode;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Zipping;
import autodiff.ui.JGraphXTools;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import multij.swing.SwingTools;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract interface NodeProcessor extends Serializable {
	
	public abstract Map<Node<?>, List<Node<?>>> getForwards();
	
	public abstract Map<Node<?>, List<Node<?>>> getBackwards();
	
	public abstract NodeVisitor<Void> getForwarder();
	
	public default <N extends Node<?>> N fill(final N node, final float value) {
		final int n = node.getLength();
		
		for (int i = 0; i < n; ++i) {
			node.set(i, value);
		}
		
		return node;
	}
	
	public default <N extends Node<?>> List<Node<?>> collectForward(final N node) {
		return this.getForwards().computeIfAbsent(node, __ -> {
			final List<Node<?>> result = new ArrayList<>(node.accept(new ForwardCollector(true)));
			
			reverse(result);
			
			return result;
		});
	}
	
	public default <N extends Node<?>> List<Node<?>> collectBackwardDiff(final N node) {
		return this.getBackwards().computeIfAbsent(node, __ -> {
			final Collection<Node<?>> forwardNodes = node.accept(new ForwardCollector(true));
			final List<Node<?>> result = new ArrayList<>(node.accept(new BackwardDiffCollector(true)));
			
			result.removeAll(forwardNodes);
			
			reverse(result);
			
			if ("show graph".equals("")) {
				SwingTools.show(JGraphXTools.newGraphComponent(result, 160, 50), "view", false);
			}
			
			return result;
		});
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
		
		private final boolean unfolding;
		
		private final Collection<Node<?>> result;
		
		public ForwardCollector(final boolean unfolding) {
			this.unfolding = unfolding;
			this.result = new LinkedHashSet<>();
		}
		
		public final boolean isUnfolding() {
			return this.unfolding;
		}
		
		public final Collection<Node<?>> getResult() {
			return this.result;
		}
		
		@Override
		public final Collection<Node<?>> visit(final Node<?> node) {
			// for ordered collections, make sure this is added after its dependents
			this.result.remove(node);
			this.result.add(node);
			
			node.getArguments().forEach(a -> a.accept(this));
			node.getAdditionalDependencies().forEach(a -> a.accept(this));
			
			return this.getResult();
		}
		
		@Override
		public final Collection<Node<?>> visit(final CustomNode node) {
			return this.isUnfolding() ? node.unfold().accept(this) : this.visit((Node<?>) node);
		}
		
		private static final long serialVersionUID = 7381617866288668668L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-02)
	 */
	public static final class BackwardDiffCollector implements NodeVisitor<Collection<Node<?>>> {
		
		private final Collection<Node<?>> done;
		
		private final ForwardCollector forwardCollector;
		
		public BackwardDiffCollector(final boolean unfolding) {
			this.done = new HashSet<>();
			this.forwardCollector = new ForwardCollector(unfolding);
		}
		
		@Override
		public final Collection<Node<?>> visit(final Node<?> node) {
			node.getArguments().forEach(a -> a.accept(this));
			node.getAdditionalDependencies().forEach(a -> a.accept(this));
			
			return this.forwardCollector.getResult();
		}
		
		@Override
		public final Collection<Node<?>> visit(final Mapping node) {
			if (!this.done.add(node)) {
				return this.forwardCollector.getResult();
			}
			
			if (node.getArgument().getDiffs() != null) {
				final String diffName = Functions.diffName(node.getFunctionName(), 0);
				final Mapping df0 = new Mapping().setFunctionName(diffName)
						.setArgument(node.getArgument()).autoShape();
				
				new Zipping().setFunctionName("*")
				.setLeft(node.getDiffs()).setRight(df0)
				.setByteBuffer(node.getArgument().getDiffs()).autoShape()
				.accept(this.forwardCollector);
			}
			
			return this.visit((Node<?>) node);
		}
		
		@Override
		public final Collection<Node<?>> visit(final Zipping node) {
			if (!this.done.add(node)) {
				return this.forwardCollector.getResult();
			}
			
			final Node<?> left = node.getLeft();
			final Node<?> right = node.getRight();
			final Node<?> leftDiffs = left.getDiffs();
			final Node<?> rightDiffs = right.getDiffs();
			
			if (leftDiffs != null) {
				final String leftDiffName = Functions.diffName(node.getFunctionName(), 0);
				final Zipping df0 = new Zipping().setFunctionName(leftDiffName)
						.setLeft(left).setRight(right).autoShape();
				final Zipping dfd0 = new Zipping().setFunctionName("*")
						.setLeft(node.getDiffs()).setRight(df0).setByteBuffer(leftDiffs).setShape(leftDiffs.getLength());
				
				dfd0.accept(this.forwardCollector);
			}
			
			if (rightDiffs != null) {
				final String rightDiffName = Functions.diffName(node.getFunctionName(), 1);
				final Zipping df1 = new Zipping().setFunctionName(rightDiffName)
						.setLeft(left).setRight(right).autoShape();
				final Zipping dfd1 = new Zipping().setFunctionName("*")
						.setLeft(node.getDiffs()).setRight(df1).setByteBuffer(rightDiffs).setShape(rightDiffs.getLength());
				
				dfd1.accept(this.forwardCollector);
			}
			
			return this.visit((Node<?>) node);
		}
		
		@Override
		public final Collection<Node<?>> visit(final MatrixMultiplication node) {
			if (!this.done.add(node)) {
				return this.forwardCollector.getResult();
			}
			
			final Node<?> a = node.getLeft();
			final Node<?> b = node.getRight();
			final Node<?> aDiffs = a.getDiffs();
			final Node<?> bDiffs = b.getDiffs();
			final Node<?> cDiffs = node.getDiffs();
			
			/*
			 * C += A B
			 *   A.diff += C.diff B'
			 * 
			 * C += A' B
			 *   A.diff += B C'.diff
			 * 
			 * C += A' B'
			 *   A.diff += B' C'.diff
			 * 
			 * C += A B'
			 *   A.diff += C.diff B
			 */
			
			if (aDiffs != null) {
				if (node.isTransposeLeft()) {
					new MatrixMultiplication()
					.setLeft(b).setTransposeLeft(node.isTransposeRight())
					.setRight(cDiffs).setTransposeRight(true)
					.setByteBuffer(aDiffs).autoShape()
					.accept(this.forwardCollector);
				} else {
					new MatrixMultiplication()
					.setLeft(cDiffs)
					.setRight(b).setTransposeRight(!node.isTransposeRight())
					.setByteBuffer(aDiffs).autoShape()
					.accept(this.forwardCollector);
				}
			}
			
			/*
			 * C += A B
			 *   B.diff += A' C.diff
			 * 
			 * C += A' B
			 *   B.diff += A C.diff
			 * 
			 * C += A' B'
			 *   B.diff += C'.diff A'
			 * 
			 * C += A B'
			 *   B.diff += C'.diff A
			 */
			
			if (bDiffs != null) {
				if (node.isTransposeRight()) {
					new MatrixMultiplication()
					.setLeft(cDiffs).setTransposeLeft(true)
					.setRight(a).setTransposeRight(node.isTransposeRight())
					.setByteBuffer(bDiffs).autoShape()
					.accept(this.forwardCollector);
				} else {
					new MatrixMultiplication()
					.setLeft(a).setTransposeLeft(!node.isTransposeLeft())
					.setRight(cDiffs)
					.setByteBuffer(bDiffs).autoShape()
					.accept(this.forwardCollector);
				}
			}
			
			return this.visit((Node<?>) node);
		}
		
		@Override
		public final Collection<Node<?>> visit(final CustomNode node) {
			if (!this.done.add(node)) {
				return this.forwardCollector.getResult();
			}
			
			return this.forwardCollector.isUnfolding() ? node.unfold().accept(this) : this.visit((Node<?>) node);
		}
		
		private static final long serialVersionUID = 7381617866288668668L;
		
	}
	
}
