package autodiff.nodes;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Mapping extends UnaryNode<Mapping> {
	
	private String functionName;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final String getFunctionName() {
		return this.functionName;
	}
	
	public final Mapping setFunctionName(final String functionName) {
		this.functionName = functionName;
		
		return this;
	}
	
	@Override
	public final Mapping autoShape() {
		return this.setShape(this.getArgument().getShape());
	}
	
	private static final long serialVersionUID = -2566458738220643925L;
	
}
