package autodiff.nodes;

import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-08-02)
 */
public abstract class CustomNode extends AbstractNode<CustomNode> {
	
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
	
	@Override
	public final boolean setupDiffs() {
		return this.isUnfolded() ? super.setupDiffs() : this.unfold().setupDiffs();
	}
	
	protected abstract Node<?> doUnfold();
	
	private static final long serialVersionUID = 4346086087721017293L;
	
}
