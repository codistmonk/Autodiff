package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Selection extends BinaryNode<Selection> {
	
	private int stride;
	
	private int offsetStride;
	
	public final int getStride() {
		return this.stride;
	}
	
	public final Selection setStride(final int stride) {
		this.stride = stride;
		
		return this;
	}
	
	public final int getOffsetStride() {
		return this.offsetStride;
	}
	
	public final Selection setOffsetStride(final int offsetStride) {
		this.offsetStride = offsetStride;
		
		return this;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final Selection setVectors(final Node<?> vectors) {
		return this.setLeft(vectors);
	}
	
	public final Node<?> getVectors() {
		return this.getLeft();
	}
	
	public final Selection setIndices(final Node<?> indices) {
		return this.setRight(indices);
	}
	
	public final Node<?> getIndices() {
		return this.getRight();
	}
	
	@Override
	public final Selection autoShape() {
		if (this.getStride() <= 0) {
			this.setStride(this.getVectors().getLength());
		}
		
		final int m = this.getVectors().getLength();
		final int n = this.getStride();
		
		Node.check(m % n == 0, () -> "Invalid stride: " + m + " not divisible by " + n);
		
		if (n < m) {
			return this.setShape(m / n, this.getIndices().getLength());
		}
		
		return this.setShape(this.getIndices().getShape());
	}
	
	private static final long serialVersionUID = 1629560466184869676L;
	
}
