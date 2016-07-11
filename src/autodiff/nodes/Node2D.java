package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public interface Node2D<N extends Node2D<?>> extends Node<N> {
	
	public abstract int getOffsetX();
	
	public abstract N setOffsetX(int offsetX);
	
	public abstract int getOffsetY();
	
	public abstract N setOffsetY(int offsetY);
	
	public abstract int getStrideX();
	
	public abstract N setStrideX(int offsetX);
	
	public abstract int getStrideY();
	
	public abstract N setStrideY(int offsetY);
	
	@Override
	public default N autoShape() {
		final int[] shape = this.getArguments().get(0).getShape().clone();
		final int h = shape[shape.length - 2];
		final int w = shape[shape.length - 1];
		
		shape[shape.length - 2] = (h - this.getOffsetY() + this.getStrideY() - 1) / this.getStrideY();
		shape[shape.length - 1] = (w - this.getOffsetX() + this.getStrideX() - 1) / this.getStrideX();
		
		return this.setShape(shape);
	}
	
}
