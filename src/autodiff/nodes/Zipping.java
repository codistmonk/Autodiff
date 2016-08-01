package autodiff.nodes;

import autodiff.computing.Functions;

import java.util.ArrayList;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Zipping extends BinaryNode<Zipping> {
	
	private String functionName;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final String getFunctionName() {
		return this.functionName;
	}
	
	public final Zipping setFunctionName(final String functionName) {
		this.functionName = functionName;
		
		return this;
	}
	
	@Override
	public final Zipping autoShape() {
		return this.setShape(this.getLeft().getShape());
	}
	
	@Override
	protected final List<Node<?>> newBackwardDiffNodes() {
		final Node<?> left = this.getLeft();
		final Node<?> right = this.getRight();
		final Node<?> leftDiffs = left.getDiffs();
		final Node<?> rightDiffs = right.getDiffs();
		final List<Node<?>> result = new ArrayList<>(2);
		
		if (leftDiffs != null) {
			final String leftDiffName = Functions.diffName(this.getFunctionName(), 0);
			final Zipping df0 = new Zipping().setFunctionName(leftDiffName)
					.setLeft(left).setRight(right).autoShape();
			final Zipping dfd0 = new Zipping().setFunctionName("*")
					.setLeft(this.getDiffs()).setRight(df0).setByteBuffer(leftDiffs).setShape(leftDiffs.getLength());
			
			result.add(dfd0);
		}
		
		if (rightDiffs != null) {
			final String rightDiffName = Functions.diffName(this.getFunctionName(), 1);
			final Zipping df0 = new Zipping().setFunctionName(rightDiffName)
					.setLeft(left).setRight(right).autoShape();
			final Zipping dfd0 = new Zipping().setFunctionName("*")
					.setLeft(this.getDiffs()).setRight(df0).setByteBuffer(rightDiffs).setShape(rightDiffs.getLength());
			
			result.add(dfd0);
		}
		
		return result;
	}
	
	private static final long serialVersionUID = -846205974402244229L;
	
}
