package autodiff.nodes;

import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Data extends AbstractNode<Data> {
	
	@Override
	public final boolean isComputationNode() {
		return false;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	protected final List<Node<?>> newBackwardDiffNodes() {
		return Collections.emptyList();
	}
	
	private static final long serialVersionUID = -8666641173896611664L;
	
}
