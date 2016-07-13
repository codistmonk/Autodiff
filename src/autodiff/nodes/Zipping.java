package autodiff.nodes;

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
	
	private static final long serialVersionUID = -846205974402244229L;
	
}
