package autodiff.nodes;

import java.util.Arrays;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class BinaryNode<N extends BinaryNode<?>> extends AbstractNode<N> {
	
	protected BinaryNode() {
		super(Arrays.asList(null, null));
	}
	
	@SuppressWarnings("unchecked")
	public final N setLeft(final Node<?> left) {
		this.getArguments().set(0, left);
		
		return (N) this;
	}
	
	public final Node<?> getLeft() {
		return this.getArguments().get(0);
	}
	
	@SuppressWarnings("unchecked")
	public final N setRight(final Node<?> right) {
		this.getArguments().set(1, right);
		
		return (N) this;
	}
	
	public final Node<?> getRight() {
		return this.getArguments().get(1);
	}
	
	private static final long serialVersionUID = -8113026999773382676L;
	
}
