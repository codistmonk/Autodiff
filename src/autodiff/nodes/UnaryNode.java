package autodiff.nodes;

import java.util.Arrays;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class UnaryNode<N extends UnaryNode<?>> extends AbstractNode<N> {
	
	protected UnaryNode() {
		super(Arrays.asList((Node<?>) null));
	}
	
	@SuppressWarnings("unchecked")
	public final N setArgument(final Node<?> argument) {
		this.getArguments().set(0, argument);
		
		return (N) this;
	}
	
	public final Node<?> getArgument() {
		return this.getArguments().get(0);
	}
	
	private static final long serialVersionUID = 3018898113488053452L;
	
}
