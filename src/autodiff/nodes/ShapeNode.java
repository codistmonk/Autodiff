package autodiff.nodes;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-21)
 */
public final class ShapeNode implements Node<ShapeNode> {
	
	private final long id;
	
	private final List<Node<?>> arguments;
	
	private Node<?> diffs;
	
	private int[] shape;
	
	public ShapeNode(final Node<?> source) {
		this.id = NodesTools.nextId.getAndIncrement();
		this.arguments = Arrays.asList(source);
		this.shape = source.getShape().clone();
	}
	
	@Override
	public final long getId() {
		return this.id;
	}
	
	@Override
	public final Collection<Node<?>> getAdditionalDependencies() {
		return this.getSource().getAdditionalDependencies();
	}
	
	public final Node<?> getSource() {
		return this.getArguments().get(0);
	}
	
	@Override
	public final boolean isComputationNode() {
		return false;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final ShapeNode setShape(final int... shape) {
		Node.super.setShape(shape);
		
		this.shape = shape;
		
		final Node<?> diffs = this.getDiffs();
		
		if (diffs != null) {
			diffs.setShape(this.getShape());
		}
		
		return this;
	}
	
	@Override
	public final int[] getShape() {
		return this.shape;
	}
	
	@Override
	public final List<Node<?>> getArguments() {
		return this.arguments;
	}
	
	@Override
	public final Storage getStorage() {
		return this.getSource().getStorage();
	}
	
	@Override
	public final void setupDiffs(final boolean setupDiffs) {
		this.getSource().setupDiffs(setupDiffs);
	}
	
	@Override
	public final boolean setupDiffs() {
		return this.getSource().setupDiffs();
	}
	
	@Override
	public final Node<?> getDiffs() {
		if (this.getSource().getDiffs() != null) {
			if (this.diffs == null) {
				this.diffs = new ShapeNode(this.getSource().getDiffs()).setShape(this.getShape());
			}
		} else {
			this.diffs = null;
		}
		
		return this.diffs;
	}
	
	@Override
	public final List<Node<?>> getBackwardDiffNodes() {
		return Collections.emptyList();
	}
	
	@Override
	public final String toString() {
		return this.getSource().toString();
	}
	
	private static final long serialVersionUID = 5490211672609331940L;
	
}
