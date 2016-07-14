package autodiff.nodes;

import java.nio.ByteBuffer;
import java.nio.FloatBuffer;
import java.util.Collections;
import java.util.List;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract class AbstractNode<N extends AbstractNode<?>> implements Node<N> {
	
	private final List<Node<?>> arguments;
	
	private Node<?> diffs;
	
	private ByteBuffer byteBuffer;
	
	private FloatBuffer floatBuffer;
	
	private int[] shape;
	
	protected AbstractNode() {
		this(Collections.emptyList());
	}
	
	protected AbstractNode(final List<Node<?>> arguments) {
		this.arguments = arguments;
	}
	
	@Override
	public final int[] getShape() {
		return this.shape;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N setShape(final int... shape) {
		if (this.getByteBuffer() == null) {
			this.shape = shape;
			this.setByteBuffer(ByteBuffer.allocateDirect(Float.BYTES * this.getLength()));
		} else {
			Node.super.setShape(shape);
			this.shape = shape;
		}
		
		if (this.getDiffs() != null) {
			this.getDiffs().setShape(shape);
		}
		
		return (N) this;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N setByteBuffer(final ByteBuffer byteBuffer) {
		this.byteBuffer = byteBuffer;
		this.floatBuffer = byteBuffer.asFloatBuffer();
		
		return (N) this;
	}
	
	@Override
	public final ByteBuffer getByteBuffer() {
		return this.byteBuffer;
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
			}
		} else {
			this.diffs = null;
		}
	}
	
	@Override
	public final Node<?> getDiffs() {
		return this.diffs;
	}
	
	private static final long serialVersionUID = 8399842389497413524L;
	
}
