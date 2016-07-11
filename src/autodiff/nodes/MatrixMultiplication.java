package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class MatrixMultiplication extends BinaryNode<MatrixMultiplication> {
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final MatrixMultiplication autoShape() {
		final Node<?> left = this.getLeft();
		final Node<?> right = this.getRight();
		final int[] leftShape = left.getLengths(new int[2]);
		final int[] rightShape = right.getLengths(new int[2]);
		
		Node.checkLength(leftShape[1], rightShape[0]);
		
		return this.setShape(leftShape[0], rightShape[1]);
	}
	
	private static final long serialVersionUID = 6980459860515499847L;
	
}
