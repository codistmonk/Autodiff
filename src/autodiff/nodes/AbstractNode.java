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
	
	private final List<Node<?>> arguments;
	
	private Node<?> diffs;
	
	private transient ByteBuffer byteBuffer;
	
	private transient FloatBuffer floatBuffer;
	
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
			this.setByteBuffer(ByteBuffer.allocateDirect(Float.BYTES * this.getLength()).order(ByteOrder.nativeOrder()));
		} else {
			Node.super.setShape(shape);
			this.shape = shape;
		}
		
		if (this.getDiffs() != null) {
			this.getDiffs().setShape(shape);
		}
		
		return (N) this;
	}
	
	@SuppressWarnings("unchecked")
	public final N setByteBuffer(final ByteBuffer byteBuffer) {
		this.byteBuffer = byteBuffer;
		this.floatBuffer = byteBuffer.asFloatBuffer();
		
		return (N) this;
	}
	
	public final ByteBuffer getByteBuffer() {
		return this.byteBuffer;
	}
	
	public final FloatBuffer getFloatBuffer() {
		return this.floatBuffer;
	}
	
	@Override
	public final float[] get(final float[] result) {
		Node.checkLength(this.getLength(), result.length);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().get(result);
		
		return result;
	}
	
	@Override
	public final float get(final int index) {
		return this.getFloatBuffer().get(index);
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N set(final float... values) {
		if (this.getShape() == null) {
			this.setShape(values.length);
		}
		
		Node.checkLength(this.getLength(), values.length);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().put(values);
		
		return (N) this;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	public final N set(final int index, final float value) {
		this.getFloatBuffer().put(index, value);
		
//		if (!Float.isFinite(value)) {
//			throw new RuntimeException(index + ": " + value);
//		}
		
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
	
}
