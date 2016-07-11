package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Convolution2D extends BinaryNode<Convolution2D> implements Node2D<Convolution2D> {
	
	private int offsetX;
	
	private int offsetY;
	
	private int strideX = 1;
	
	private int strideY = 1;
	
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
	public final int getOffsetX() {
		return this.offsetX;
	}
	
	@Override
	public final Convolution2D setOffsetX(final int offsetX) {
		this.offsetX = offsetX;
		
		return this;
	}
	
	@Override
	public final int getOffsetY() {
		return this.offsetY;
	}
	
	@Override
	public final Convolution2D setOffsetY(final int offsetY) {
		this.offsetY = offsetY;
		
		return this;
	}
	
	@Override
	public final int getStrideX() {
		return this.strideX;
	}
	
	@Override
	public final Convolution2D setStrideX(final int strideX) {
		this.strideX = strideX;
		
		return this;
	}
	
	@Override
	public final int getStrideY() {
		return this.strideY;
	}
	
	@Override
	public final Convolution2D setStrideY(final int strideY) {
		this.strideY = strideY;
		
		return this;
	}
	
	private static final long serialVersionUID = -3377967560676134755L;
	
}
