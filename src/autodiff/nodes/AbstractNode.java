package autodiff.nodes;

import static autodiff.nodes.NodesTools.newId;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class AbstractNode<N extends AbstractNode<?>> implements Node<N> {
	
	private long id;
	
	private final List<Node<?>> arguments;
	
	private final Data values;
	
	protected AbstractNode() {
		this(Collections.emptyList());
	}
	
	protected AbstractNode(final List<Node<?>> arguments) {
		this.id = newId();
		this.arguments = arguments;
		this.values = new Data();
	}
	
	@Override
	public final long getId() {
		return this.id;
	}
	
	public final Data getValues() {
		return this.values;
	}
	
	@Override
	public final int[] getShape() {
		return this.getValues().getShape();
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N setShape(final int... shape) {
		this.getValues().setShape(shape);
		
		this.getStorage().getContributors().add(this);
		
		return (N) this;
	}
	
	@Override
	public final Storage getStorage() {
		return this.getValues().getStorage();
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N setStorage(final Node<?> node) {
		node.getStorage().getContributors().add(this);
		
		this.getValues().setStorage(node.getStorage());
		
		return (N) this;
	}
	
	@Override
	public final List<Node<?>> getArguments() {
		return this.arguments;
	}
	
	@Override
	public final void setupDiffs(final boolean setupDiffs) {
		this.getValues().setupDiffs(setupDiffs);
	}
	
	@Override
	public final Node<?> getDiffs() {
		return this.getValues().getDiffs();
	}
	
	@Override
	public final String toString() {
		return Arrays.toString(this.get(new float[this.getLength()]));
	}
	
	private final void readObject(final ObjectInputStream in) throws ClassNotFoundException, IOException {
		in.defaultReadObject();
		this.id = newId();
	}
	
	private static final long serialVersionUID = 8399842389497413524L;
	
}
