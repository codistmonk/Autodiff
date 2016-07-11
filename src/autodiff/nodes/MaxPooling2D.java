package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class MaxPooling2D extends UnaryNode<MaxPooling2D> implements Node2D<MaxPooling2D> {
	
	private int offsetX;
	
	private int offsetY;
	
	private int strideX = 1;
	
	private int strideY = 1;
	
	private int kernelWidth = 1;
	
	private int kernelHeight = 1;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final int getOffsetX() {
		return this.offsetX;
	}
	
	@Override
	public final MaxPooling2D setOffsetX(final int offsetX) {
		this.offsetX = offsetX;
		
		return this;
	}
	
	@Override
	public final int getOffsetY() {
		return this.offsetY;
	}
	
	@Override
	public final MaxPooling2D setOffsetY(final int offsetY) {
		this.offsetY = offsetY;
		
		return this;
	}
	
	@Override
	public final int getStrideX() {
		return this.strideX;
	}
	
	@Override
	public final MaxPooling2D setStrideX(final int strideX) {
		this.strideX = strideX;
		
		return this;
	}
	
	@Override
	public final int getStrideY() {
		return this.strideY;
	}
	
	@Override
	public final MaxPooling2D setStrideY(final int strideY) {
		this.strideY = strideY;
		
		return this;
	}
	
	public final int getKernelWidth() {
		return this.kernelWidth;
	}
	
	public final MaxPooling2D setKernelWidth(final int kernelWidth) {
		this.kernelWidth = kernelWidth;
		
		return this;
	}
	
	public final int getKernelHeight() {
		return this.kernelHeight;
	}
	
	public final MaxPooling2D setKernelHeight(final int kernelHeight) {
		this.kernelHeight = kernelHeight;
		
		return this;
	}
	
	private static final long serialVersionUID = 1919526061727846118L;
	
}
