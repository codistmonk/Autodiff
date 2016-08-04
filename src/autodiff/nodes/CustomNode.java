package autodiff.nodes;

import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-08-02)
 */
public abstract class CustomNode<N extends CustomNode<?>> extends AbstractNode<N> {
	
	private Node<?> unfolded;
	
	protected CustomNode() {
		this(Collections.emptyList());
	}
	
	protected CustomNode(final List<Node<?>> arguments) {
		super(arguments);
	}
	
	public final boolean isUnfolded() {
		return this.unfolded != null;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@SuppressWarnings("unchecked")
	public final N reset() {
		this.unfolded = null;
		
		return (N) this;
	}
	
	public final Node<?> unfold() {
		if (this.unfolded == null) {
			this.unfolded = this.doUnfold();
		}
		
		return this.unfolded;
	}
	
	protected abstract Node<?> doUnfold();
	
	private static final long serialVersionUID = 4346086087721017293L;
	
}
