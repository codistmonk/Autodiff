package autodiff.nodes;

import static autodiff.nodes.NodesTools.checkLength;
import static autodiff.nodes.NodesTools.product;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Data implements Node<Data> {
	
	private final long id;
	
	private Storage storage;
	
	private int[] shape;
	
	private Node<?> diffs;
	
	{
		this.id = NodesTools.nextId.getAndIncrement();
	}
	
	@Override
	public final int[] getShape() {
		return this.shape;
	}
	
	@Override
	public final Data setShape(final int... shape) {
		if (this.getShape() == null) {
			this.shape = shape;
		} else {
			checkLength(this.getLength(), product(shape));
			this.shape = shape;
		}
		
		if (this.getStorage() == null) {
			this.storage = new Storage(this.getLength());
		}
		
		if (this.getDiffs() != null) {
			this.getDiffs().setShape(shape);
		}
		
		return this;
	}
	
	@Override
	public final Storage getStorage() {
		return this.storage;
	}
	
	@Override
	public final Data setStorage(final Node<?> node) {
		if (this.getShape() != null) {
			NodesTools.checkLength(this.getLength(), node.getLength());
		}
		
		final Storage oldStorage = this.getStorage();
		final Storage newStorage = node.getStorage();
		
		if (oldStorage != newStorage) {
			this.storage = newStorage;
			
			if (newStorage != null && oldStorage != null) {
				newStorage.getContributors().addAll(oldStorage.getContributors());
			}
		}
		
		if (this.getShape() == null) {
			this.setShape(node.getShape());
		}
		
		return this;
	}
	
	@Override
	public final long getId() {
		return this.id;
	}
	
	@Override
	public final List<Node<?>> getArguments() {
		return new ArrayList<>(this.getStorage().getContributors());
	}
	
	@Override
	public final boolean isComputationNode() {
		return false;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
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
	
	public final void setStorage(final Storage storage) {
		this.storage = storage;
	}
	
	@Override
	public final Node<?> getDiffs() {
		return this.diffs;
	}
	
	@Override
	public final String toString() {
		return Arrays.toString(this.get(new float[this.getLength()]));
	}
	
	private static final long serialVersionUID = -8666641173896611664L;
	
}
