package autodiff.nodes;

import static autodiff.nodes.NodesTools.*;
import static multij.tools.Tools.swap;

import java.util.ArrayList;
import java.util.List;

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
	protected final List<Node<?>> newBackwardDiffNodes() {
		final Node<?> a = this.getLeft();
		final Node<?> b = this.getRight();
		final Node<?> aDiffs = a.getDiffs();
		final Node<?> bDiffs = b.getDiffs();
		final Node<?> cDiffs = this.getDiffs();
		final List<Node<?>> result = new ArrayList<>(2);
		
		/*
		 * C += A B
		 *   A.diff += C.diff B'
		 * 
		 * C += A' B
		 *   A.diff += B C'.diff
		 * 
		 * C += A' B'
		 *   A.diff += B' C'.diff
		 * 
		 * C += A B'
		 *   A.diff += C.diff B
		 */
		
		if (aDiffs != null) {
			if (this.isTransposeLeft()) {
				result.add(new MatrixMultiplication()
				.setLeft(b).setTransposeLeft(this.isTransposeRight())
				.setRight(cDiffs).setTransposeRight(true)
				.setByteBuffer(aDiffs).autoShape());
			} else {
				result.add(new MatrixMultiplication()
				.setLeft(cDiffs)
				.setRight(b).setTransposeRight(!this.isTransposeRight())
				.setByteBuffer(aDiffs).autoShape());
			}
		}
		
		/*
		 * C += A B
		 *   B.diff += A' C.diff
		 * 
		 * C += A' B
		 *   B.diff += A C.diff
		 * 
		 * C += A' B'
		 *   B.diff += C'.diff A'
		 * 
		 * C += A B'
		 *   B.diff += C'.diff A
		 */
		
		if (bDiffs != null) {
			if (this.isTransposeRight()) {
				result.add(new MatrixMultiplication()
				.setLeft(cDiffs).setTransposeLeft(true)
				.setRight(a).setTransposeRight(this.isTransposeRight())
				.setByteBuffer(bDiffs).autoShape());
			} else {
				result.add(new MatrixMultiplication()
				.setLeft(a).setTransposeLeft(!this.isTransposeLeft())
				.setRight(cDiffs)
				.setByteBuffer(bDiffs).autoShape());
			}
		}
		
		return result;
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
