package autodiff.computing;

import static multij.tools.Tools.cast;
import static multij.tools.Tools.debugPrint;
import static org.jocl.CL.CL_MEM_READ_WRITE;
import static org.jocl.CL.CL_MEM_USE_HOST_PTR;
import static org.jocl.CL.setExceptionsEnabled;
import autodiff.cl.CLContext;
import autodiff.cl.CLKernel;
import autodiff.nodes.AbstractNode;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Selection;

import java.nio.Buffer;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;
import java.nio.LongBuffer;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.jocl.Pointer;
import org.jocl.Sizeof;
import org.jocl.cl_mem;

/**
 * @author codistmonk (creation 2016-07-17)
 */
public final class CLProcessor implements NodeProcessor {
	
	private final CLContext context;
	
	private final Map<Object, Pointer> clPointers;
	
	private final Map<Object, cl_mem> clBuffers;
	
	private final Forwarder forwarder;
	
	private final BackwardDiffer backwardDiffer;
	
	public CLProcessor() {
		this(new CLContext());
	}
	
	public CLProcessor(final CLContext context) {
		this.context = context;
		this.clPointers = new IdentityHashMap<>();
		this.clBuffers = new IdentityHashMap<>();
		this.forwarder = this.new Forwarder();
		this.backwardDiffer = this.new BackwardDiffer();
	}
	
	public final CLContext getContext() {
		return this.context;
	}
	
	@Override
	public final NodeVisitor<Void> getForwarder() {
		return this.forwarder;
	}
	
	@Override
	public final NodeVisitor<Void> getBackwardDiffer() {
		return this.backwardDiffer;
	}
	
	@Override
	public final <N extends Node<?>> N fullForward(final N node) {
		final Node<?>[] nodes = node.collectTo(new LinkedHashSet<>()).toArray(new Node[0]);
		
		debugPrint(nodes.length);
		
		final StringBuilder programSourceBuilder = new StringBuilder();
		final Map<Node<?>, String> nodeNames = new HashMap<>();
		
		programSourceBuilder.append("__kernel void net(");
		
		for (int i = 0; i < nodes.length; ++i) {
			final Node<?> n = nodes[i];
			
			if (n instanceof Data) {
				final String nodeName = "data_" + nodeNames.size();
				
				nodeNames.put(n, nodeName);
				
				programSourceBuilder.append("__global float const * const ").append(nodeName).append(", ");
			}
		}
		
		nodeNames.put(node, "result");
		
		programSourceBuilder.append("__global float * const result) {\n");
		
		{
			final Selection selection = cast(Selection.class, node);
			
			if (selection != null) {
				final String vectorsName = nodeNames.get(selection.getVectors());
				final String indicesName = nodeNames.get(selection.getIndices());
				
				debugPrint(vectorsName);
				debugPrint(indicesName);
				
				final int m = selection.getVectors().getLength();
				final int n = selection.getIndices().getLength();
				final int stride = m / n;
				
				programSourceBuilder.append("	int const gid = get_global_id(0);\n");
				programSourceBuilder.append("	int const stride = ").append(stride).append(";\n");
				programSourceBuilder.append("	result[gid * stride] = ").append(vectorsName).append("[gid * stride + (int) ").append(indicesName).append("[gid]];\n");
				programSourceBuilder.append("}\n");
				
				debugPrint("\n" + programSourceBuilder);
				
				CLKernel net = null;
				
				try {
					net = this.getContext().createAndBuildProgram(programSourceBuilder.toString()).createKernel("net");
					net.setArg(0, this.clBuffer((AbstractNode<?>) selection.getVectors()));
					net.setArg(1, this.clBuffer((AbstractNode<?>) selection.getIndices()));
					net.setArg(2, this.clBuffer(selection));
					net.enqueueNDRange(node.getLength());
					this.getContext().getDefaultCommandQueue().enqueueReadBuffer(this.clBuffer(selection), Sizeof.cl_float * selection.getLength(), this.pointer(selection));
				} finally {
					if (net != null) {
						net.release();
					}
				}
			}
		}
		
		return null;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		// TODO Auto-generated method stub
		return null;
	}
	
	final cl_mem clBuffer(final AbstractNode<?> node) {
		return this.clBuffers.computeIfAbsent(node, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Float.BYTES, node.getLength(),
				this.pointer(node)));
	}
	
	final Pointer pointer(final AbstractNode<?> node) {
		return this.clPointers.computeIfAbsent(node, __ -> Pointer.toBuffer(node.getFloatBuffer().position(0)));
	}
	
	final cl_mem clBuffer(final LongBuffer buffer) {
		return this.clBuffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Long.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final cl_mem clBuffer(final IntBuffer buffer) {
		return this.clBuffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Integer.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final cl_mem clBuffer(final FloatBuffer buffer) {
		return this.clBuffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Float.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final Pointer pointer(final Buffer buffer) {
		return this.clPointers.computeIfAbsent(buffer, __ -> Pointer.toBuffer(buffer));
	}
	
	/**
	 * @author codistmonk (creation 2016-07-17)
	 */
	private final class Forwarder implements NodeVisitor<Void> {
		
		Forwarder() {
			// NOP
		}
		
		private static final long serialVersionUID = 8143280110227329187L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-17)
	 */
	private final class BackwardDiffer implements NodeVisitor<Void> {
		
		BackwardDiffer() {
			// NOP
		}
		
		private static final long serialVersionUID = -2609588837130668886L;
		
	}
	
	private static final long serialVersionUID = -7097287103829755831L;
	
	public static final CLProcessor INSTANCE = new CLProcessor();
	
	static {
        setExceptionsEnabled(true);
	}
	
	static final String getAddressSource() {
		return "__kernel void "
				+ "getAddress(__global void const * const a,"
				+ "              __global intptr_t * const result)\n"
				+ "{\n"
				+ "    result[0] = a;\n"
				+ "}";
	}
	
	static final String getFill0Source() {
		return getFillSource(0F, "0");
	}
	
	static final String getFill1Source() {
		return getFillSource(1F, "1");
	}
	
	static final String getFillSource(final float x, final String nameSuffix) {
		return "__kernel void "
				+ "fill" + nameSuffix + "(__global float * const a)\n"
				+ "{\n"
				+ "    a[get_global_id(0)] = " + x + ";\n"
				+ "}";
	}
	
	public static final long guessLocalWorkSize(final long globalSize, final long m) {
		for (long result = m; 1L < result; --result) {
			if (0L == (globalSize % result)) {
				return result;
			}
		}
		
		return 1L;
	}
	
}
