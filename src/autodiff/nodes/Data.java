package autodiff.nodes;

import static autodiff.nodes.NodesTools.checkLength;
import static autodiff.nodes.NodesTools.product;
import static multij.tools.Tools.cast;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Data implements Node<Data> {
	
	private final long id;
	
	private Storage storage;
	
	private int[] shape;
	
	private Node<?> diffs;
	
	{
		this.id = NodesTools.nextId();
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
			this.setStorage(new Storage(this.getLength()));
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
			this.setStorage(newStorage);
			
			if (newStorage != null && oldStorage != null) {
				for (final Node<?> n : oldStorage.getContributors()) {
					n.setStorage(node);
				}
				
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
//		return new ArrayList<>(this.getStorage().getContributors());
		return this.getStorage().getContributors().stream().filter(n -> {
			if (n instanceof Data) {
				return false;
			}
			
			final CustomNode customNode = cast(CustomNode.class, n);
			
			if (customNode != null && customNode.isUnfolded()) {
				return false;
			}
			
			return true;
		}).collect(Collectors.toList());
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
				
				for (final Node<?> n : this.getStorage().getContributors()) {
					n.setupDiffs(setupDiffs);
					n.getDiffs().setStorage(this.getDiffs());
				}
			}
		} else {
			this.diffs = null;
		}
	}
	
	@Override
	public final boolean setupDiffs() {
		boolean needSetup = false;
		
		for (final Node<?> n : this.getStorage().getContributors()) {
			if (!(n instanceof Data)) {
				needSetup |= n.setupDiffs();
			} else {
				needSetup |= n.hasDiffs();
			}
		}
		
		this.setupDiffs(needSetup);
		
		return this.hasDiffs();
	}
	
	public final void setStorage(final Storage storage) {
		if (this.storage != null && storage != null) {
			final int n = storage.getLength();
			
			for (int i = 0; i < n; ++i) {
				storage.getFloatBuffer().put(i, storage.getFloatBuffer().get(i) + this.storage.getFloatBuffer().get(i));
			}
		}
		
		this.storage = storage;
		this.storage.getContributors().add(this);
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
