package autodiff.nodes;

import java.util.Arrays;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Sum extends UnaryNode<Sum> {
	
	private int stride;
	
	public final int getStride() {
		return this.stride;
	}
	
	public final Sum setStride(final int stride) {
		this.stride = stride;
		
		return this;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final Sum autoShape() {
		final int[] argumentShape = this.getArgument().getShape();
		final int[] shape;
		
		if (this.getStride() <= 0) {
			this.setStride(argumentShape[argumentShape.length - 1]);
		}
		
		final int n = this.getArgument().getLength();
		
		Node.check(n % this.getStride() == 0, () -> "Bad argument: " + n + " not divisible by " + this.getStride());
		
		int j = argumentShape.length - 1;
		
		for (int tmp = argumentShape[j]; tmp < this.getStride(); tmp *= argumentShape[j], --j) {
			// NOP
		}
		
		shape = Arrays.copyOf(argumentShape, j);
		
		return this.setShape(shape);
	}
	
	private static final long serialVersionUID = -6072283819791282067L;
	
}
