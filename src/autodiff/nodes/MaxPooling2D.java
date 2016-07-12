package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class MaxPooling2D extends UnaryNode<MaxPooling2D> implements Node2D<MaxPooling2D> {
	
	private final int[] offsets = { 0, 0, 0, 0 };
	
	private final int[] strides = { 1, 1 };
	
	private final int[] kernelShape = { 1, 1 };
	
	public final Node<?> getInputs() {
		return this.getArgument();
	}
	
	public final MaxPooling2D setInputs(final Node<?> inputs) {
		return this.setArgument(inputs);
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
	
	public final int[] getKernelShape() {
		return this.kernelShape;
	}
	
	public final MaxPooling2D setKernelSide(final int kernelSide) {
		return this.setKernelShape(kernelSide, kernelSide);
	}
	
	public final MaxPooling2D setKernelShape(final int width, final  int height) {
		final int[] shape = this.getKernelShape();
		
		shape[WIDTH] = width;
		shape[HEIGHT] = height;
		
		return this;
	}
	
	private static final long serialVersionUID = 1919526061727846118L;
	
	public static final int HEIGHT = 0;
	
	public static final int WIDTH = 1;
	
}
