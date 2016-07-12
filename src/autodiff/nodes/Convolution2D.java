package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Convolution2D extends BinaryNode<Convolution2D> implements Node2D<Convolution2D> {
	
	private final int[] offsets = { 0, 0, 0, 0 };
	
	private final int[] strides = { 1, 1 };
	
	public final Node<?> getInputs() {
		return this.getLeft();
	}
	
	public final Convolution2D setInputs(final Node<?> inputs) {
		return this.setLeft(inputs);
	}
	
	public final Node<?> getKernel() {
		return this.getRight();
	}
	
	public final Convolution2D setKernel(final Node<?> kernel) {
		return this.setRight(kernel);
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final int[] getOffsets() {
		return this.offsets;
	}
	
	@Override
	public final int[] getStrides() {
		return this.strides;
	}
	
	private static final long serialVersionUID = -3377967560676134755L;
	
}
