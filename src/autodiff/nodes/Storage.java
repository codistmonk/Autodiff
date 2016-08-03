package autodiff.nodes;

import static autodiff.nodes.NodesTools.checkLength;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;

/**
 * @author codistmonk (creation 2016-08-03)
 */
public final class Storage implements Serializable {
	
	private final int length;
	
	private transient ByteBuffer byteBuffer;
	
	private transient int byteOffset;
	
	private transient FloatBuffer floatBuffer;
	
	public Storage(final int length) {
		this.length = length;
		
		this.allocate();
	}
	
	public final int getLength() {
		return this.length;
	}
	
	public final ByteBuffer getByteBuffer() {
		return this.byteBuffer;
	}
	
	public final int getByteOffset() {
		return this.byteOffset;
	}
	
	public final FloatBuffer getFloatBuffer() {
		return this.floatBuffer;
	}
	
	public final float[] get(final float[] result) {
		checkLength(this.getLength(), result.length);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().get(result);
		
		return result;
	}
	
	public final Storage set(final float... values) {
		checkLength(this.getLength(), values.length);
		
		this.getFloatBuffer().position(0);
		this.getFloatBuffer().put(values);
		
		return this;
	}
	
	private final void allocate() {
		this.setByteBuffer(ByteBuffer.allocateDirect(Float.BYTES * this.getLength()).order(ByteOrder.nativeOrder()));
	}
	
	private final void setByteBuffer(final ByteBuffer byteBuffer) {
		this.byteBuffer = byteBuffer;
		this.byteOffset = byteBuffer.position();
		this.floatBuffer = byteBuffer.asFloatBuffer();
	}
	
	private final void writeObject(final ObjectOutputStream out) throws IOException {
		out.defaultWriteObject();
		out.writeObject(this.get(new float[this.getLength()]));
	}
	
	private final void readObject(final ObjectInputStream in) throws ClassNotFoundException, IOException {
		in.defaultReadObject();
		
		this.allocate();
		
		this.set((float[]) in.readObject());
	}
	
	private static final long serialVersionUID = -5827485133691923306L;
	
}
