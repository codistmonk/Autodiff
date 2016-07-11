package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Mapping extends UnaryNode<Mapping> {
	
	private String operation;
	
	public final String getOperation() {
		return this.operation;
	}
	
	public final Mapping setOperation(final String operation) {
		this.operation = operation;
		
		return this;
	}
	
	@Override
	public final Mapping autoShape() {
		return this.setShape(this.getArgument().getShape());
	}
	
	private static final long serialVersionUID = -2566458738220643925L;
	
}
