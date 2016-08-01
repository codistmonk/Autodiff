package autodiff.nodes;

import java.util.Arrays;
import java.util.List;

import autodiff.computing.Functions;

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
	protected final List<Node<?>> newBackwardDiffNodes() {
		final String diffName = Functions.diffName(this.getFunctionName(), 0);
		final Mapping df0 = new Mapping().setFunctionName(diffName)
				.setArgument(this.getArgument()).autoShape();
		
		return Arrays.asList(new Zipping().setFunctionName("*")
				.setLeft(this.getDiffs()).setRight(df0)
				.setByteBuffer(this.getArgument().getDiffs()).autoShape());
	}
	
	@Override
	public final Mapping autoShape() {
		return this.setShape(this.getArgument().getShape());
	}
	
	private static final long serialVersionUID = -2566458738220643925L;
	
}
