package autodiff.nodes;

import java.util.List;

/**
 * @author codistmonk (creation 2016-08-02)
 */
public abstract class CustomNode extends AbstractNode<CustomNode> {
	
	private Node<?> unfolded;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final CustomNode reset() {
		this.unfolded = null;
		
		return this;
	}
	
	public final Node<?> unfold() {
		if (this.unfolded == null) {
			this.unfolded = this.doUnfold();
		}
		
		return this.unfolded;
	}
	
	protected abstract Node<?> doUnfold();
	
	@Override
	protected final List<Node<?>> newBackwardDiffNodes() {
		return this.unfold().getBackwardDiffNodes();
	}
	
	private static final long serialVersionUID = 4346086087721017293L;
	
}
