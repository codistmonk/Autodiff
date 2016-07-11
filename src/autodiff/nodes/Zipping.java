package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Zipping extends BinaryNode<Zipping> {
	
	private String operation;
	
	public final String getOperation() {
		return this.operation;
	}
	
	public final Zipping setOperation(final String operation) {
		this.operation = operation;
		
		return this;
	}
	
	@Override
	public final Zipping autoShape() {
		return this.setShape(this.getLeft().getShape());
	}
	
	private static final long serialVersionUID = -846205974402244229L;
	
}
