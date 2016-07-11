package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Data extends AbstractNode<Data> {
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	private static final long serialVersionUID = -8666641173896611664L;
	
}
