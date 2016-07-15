package autodiff.nodes;

import static multij.tools.Tools.intRange;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Sum extends UnaryNode<Sum> {
	
	private int[] strides;
	
	public final int[] getStrides() {
		return this.strides;
	}
	
	public final Sum setStrides(final int... strides) {
		this.strides = strides;
		
		return this;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final Sum autoShape() {
		if (this.getStrides() == null) {
			this.setStrides(this.getArgument().getLength());
		}
		
		final int m = this.getStrides().length;
		final int[] lengths = this.getArgument().getLengths(new int[m]);
		final int[] shape = new int[m];
		
		for (final int i : intRange(m)) {
			final int n = lengths[i];
			final int s = this.getStrides()[i];
			
			Node.check(n % s == 0, () -> "Bad argument: length(" + m + " " + i + ")=" + n + " not divisible by " + s);
			
			shape[i] = lengths[i] / s;
		}
		
		return this.setShape(shape);
	}
	
	private static final long serialVersionUID = -6072283819791282067L;
	
}
