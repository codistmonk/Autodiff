package autodiff.nodes;

import static autodiff.nodes.NodesTools.*;
import static multij.tools.Tools.swap;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class MatrixMultiplication extends BinaryNode<MatrixMultiplication> {
	
	private boolean transposeLeft;
	
	private boolean transposeRight;
	
	public final boolean isTransposeLeft() {
		return this.transposeLeft;
	}
	
	public final MatrixMultiplication setTransposeLeft(final boolean transposeLeft) {
		this.transposeLeft = transposeLeft;
		
		return this;
	}
	
	public final boolean isTransposeRight() {
		return this.transposeRight;
	}
	
	public final MatrixMultiplication setTransposeRight(final boolean transposeRight) {
		this.transposeRight = transposeRight;
		
		return this;
	}
	
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
		
		if (this.isTransposeLeft()) {
			swap(leftShape, 0, 1);
		}
		
		if (this.isTransposeRight()) {
			swap(rightShape, 0, 1);
		}
		
		checkLength(leftShape[1], rightShape[0]);
		
		return this.setShape(leftShape[0], rightShape[1]);
	}
	
	private static final long serialVersionUID = 6980459860515499847L;
	
}
