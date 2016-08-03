package autodiff.nodes;

import java.util.Arrays;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Mapping extends AbstractNode<Mapping> {
	
	private String functionName;
	
	public Mapping() {
		super(Arrays.asList((Node<?>) null));
	}
	
	public final Mapping setArgument(final Node<?> argument) {
		this.getArguments().set(0, argument);
		
		return this;
	}
	
	public final Node<?> getArgument() {
		return this.getArguments().get(0);
	}
	
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
