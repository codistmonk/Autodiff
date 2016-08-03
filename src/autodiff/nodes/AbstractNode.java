package autodiff.nodes;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class AbstractNode<N extends AbstractNode<?>> implements Node<N> {
	
	private final long id;
	
	private final Collection<Node<?>> additionalDependencies;
	
	private final List<Node<?>> arguments;
	
	private Node<?> diffs;
	
	private Storage storage;
	
	private int[] shape;
	
	protected AbstractNode() {
		this(Collections.emptyList());
	}
	
	protected AbstractNode(final List<Node<?>> arguments) {
		this.id = NodesTools.nextId.getAndIncrement();
		this.additionalDependencies = new HashSet<>();
		this.arguments = arguments;
	}
	
	@Override
	public final long getId() {
		return this.id;
	}
	
	@Override
	public final Collection<Node<?>> getAdditionalDependencies() {
		return this.additionalDependencies;
	}
	
	@Override
	public final int[] getShape() {
		return this.shape;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N setShape(final int... shape) {
		if (this.getShape() == null) {
			this.shape = shape;
		} else {
			Node.super.setShape(shape);
			this.shape = shape;
		}
		
		if (this.getStorage() == null) {
			this.storage = new Storage(this.getLength());
		}
		
		if (this.getDiffs() != null) {
			this.getDiffs().setShape(shape);
		}
		
		return (N) this;
	}
	
	@Override
	public final Storage getStorage() {
		return this.storage;
	}
	
	@SuppressWarnings("unchecked")
	public final N setByteBuffer(final Node<?> node) {
		if (this.getShape() == null) {
			this.setShape(node.getShape());
		} else {
			NodesTools.checkLength(this.getLength(), node.getLength());
		}
		
		node.getAdditionalDependencies().add(this);
		
		this.storage = node.getStorage();
		
		return (N) this;
	}
	
	@Override
	public final List<Node<?>> getArguments() {
		return this.arguments;
	}
	
	@Override
	public final void setupDiffs(final boolean setupDiffs) {
		if (setupDiffs) {
			if (!this.hasDiffs()) {
				this.diffs = new Data().setShape(this.getShape());
			}
		} else {
			this.diffs = null;
		}
	}
	
	@Override
	public final Node<?> getDiffs() {
		return this.diffs;
	}
	
	@Override
	public final String toString() {
		return Arrays.toString(this.get(new float[this.getLength()]));
	}
	
	private static final long serialVersionUID = 8399842389497413524L;
	
}
