package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public interface Node2D<N extends Node2D<?>> extends Node<N> {
	
	public abstract int[] getOffsets();
	
	public default N setOffsets(final int value) {
		return this.setOffsets(value, value);
	}
	
	public default N setOffsets(final int horizontal, final int vertical) {
		return this.setOffsets(horizontal, horizontal, vertical, vertical);
	}
	
	@SuppressWarnings("unchecked")
	public default N setOffsets(final int left, final int right, final int top, final int bottom) {
		final int[] offsets = this.getOffsets();
		
		offsets[LEFT] = left;
		offsets[RIGHT] = right;
		offsets[TOP] = top;
		offsets[BOTTOM] = bottom;
		
		return (N) this;
	}
	
	public abstract int[] getStrides();
	
	public default N setStrides(final int value) {
		return this.setStrides(value, value);
	}
	
	@SuppressWarnings("unchecked")
	public default N setStrides(final int horizontal, final int vertical) {
		final int[] strides = this.getStrides();
		
		strides[HORIZONTAL] = horizontal;
		strides[VERTICAL] = vertical;
		
		return (N) this;
	}
	
	@Override
	public default N autoShape() {
		final int[] shape = this.getArguments().get(0).getShape().clone();
		final int h = shape[shape.length - 2];
		final int w = shape[shape.length - 1];
		final int[] offsets = this.getOffsets();
		final int[] strides = this.getStrides();
		
		shape[shape.length - 1] = (w - offsets[LEFT] - offsets[RIGHT] + strides[HORIZONTAL] - 1) / strides[HORIZONTAL];
		shape[shape.length - 2] = (h - offsets[TOP] - offsets[BOTTOM] + strides[VERTICAL] - 1) / strides[VERTICAL];
		
		return this.setShape(shape);
	}
	
	public static final int LEFT = 0;
	
	public static final int RIGHT = 1;
	
	public static final int TOP = 2;
	
	public static final int BOTTOM = 3;
	
	public static final int HORIZONTAL = 0;
	
	public static final int VERTICAL = 1;
	
}
