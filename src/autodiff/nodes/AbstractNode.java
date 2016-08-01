package autodiff.nodes;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class AbstractNode<N extends AbstractNode<?>> implements Node<N> {
	
	private final long id;
	
	private final List<Node<?>> arguments;
	
	private Node<?> diffs;
	
	private List<Node<?>> backwardDiffNodes;
	
	private transient ByteBuffer byteBuffer;
	
	private transient int byteOffset;
	
	private transient FloatBuffer floatBuffer;
	
	private int[] shape;
	
	protected AbstractNode() {
		this(Collections.emptyList());
	}
	
	protected AbstractNode(final List<Node<?>> arguments) {
		this.id = NodesTools.nextId.getAndIncrement();
		this.arguments = arguments;
	}
	
	@Override
	public final long getId() {
		return this.id;
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
		
		if (this.getByteBuffer() == null) {
			this.setByteBuffer(ByteBuffer.allocateDirect(Float.BYTES * this.getLength()).order(ByteOrder.nativeOrder()));
		}
		
		if (this.getDiffs() != null) {
			this.getDiffs().setShape(shape);
		}
		
		return (N) this;
	}
	
	public final N setByteBuffer(final Node<?> node) {
		return this.setByteBuffer(getPositionedByteBuffer(node));
	}
	
	@SuppressWarnings("unchecked")
	public final N setByteBuffer(final ByteBuffer byteBuffer) {
		this.byteBuffer = byteBuffer;
		this.byteOffset = byteBuffer.position();
		this.floatBuffer = byteBuffer.asFloatBuffer();
		
		return (N) this;
	}
	
	@Override
	public final ByteBuffer getByteBuffer() {
		return this.byteBuffer;
	}
	
	@Override
	public final int getByteOffset() {
		return this.byteOffset;
	}
	
	@Override
	public final FloatBuffer getFloatBuffer() {
		return this.floatBuffer;
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
				this.backwardDiffNodes = this.newBackwardDiffNodes();
			}
		} else {
			this.diffs = null;
			this.backwardDiffNodes = null;
		}
	}
	
	@Override
	public final Node<?> getDiffs() {
		return this.diffs;
	}
	
	@Override
	public final List<Node<?>> getBackwardDiffNodes() {
		return this.backwardDiffNodes;
	}
	
	@Override
	public final String toString() {
		return Arrays.toString(this.get(new float[this.getLength()]));
	}
	
	protected abstract List<Node<?>> newBackwardDiffNodes();
	
	private final void writeObject(final ObjectOutputStream out) throws IOException {
		out.defaultWriteObject();
		out.writeObject(this.get(new float[this.getLength()]));
	}
	
	private final void readObject(final ObjectInputStream in) throws ClassNotFoundException, IOException {
		in.defaultReadObject();
		
		this.setShape(this.getShape());
		this.set((float[]) in.readObject());
	}
	
	private static final long serialVersionUID = 8399842389497413524L;
	
	public static final ByteBuffer getPositionedByteBuffer(final Node<?> node) {
		return (ByteBuffer) node.getByteBuffer().position(node.getByteOffset());
	}
	
}
