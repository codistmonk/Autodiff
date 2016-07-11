package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Selection extends BinaryNode<Selection> {
	
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
		final int m = this.getVectors().getLength();
		final int n = this.getIndices().getLength();
		
		Node.check(m % n == 0, () -> "Incompatible dimensions: " + m + " not divisible by " + n);
		
		return this.setShape(this.getIndices().getShape());
	}
	
	private static final long serialVersionUID = 1629560466184869676L;
	
}
