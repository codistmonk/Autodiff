package autodiff.computing;

import static java.util.stream.Collectors.toList;
import static org.jocl.CL.CL_MEM_READ_WRITE;
import static org.jocl.CL.CL_MEM_USE_HOST_PTR;
import static org.jocl.CL.setExceptionsEnabled;

import autodiff.cl.CLContext;
import autodiff.cl.CLKernel;
import autodiff.nodes.AbstractNode;
import autodiff.nodes.BinaryNode;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.UnaryNode;

import java.nio.Buffer;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;
import java.nio.LongBuffer;
import java.util.Arrays;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.jocl.CL;
import org.jocl.Pointer;
import org.jocl.Sizeof;
import org.jocl.cl_mem;

/**
 * @author codistmonk (creation 2016-07-17)
 */
public final class CLProcessor implements NodeProcessor {
	
	private final CLContext context;
	
	private final Map<Object, Pointer> pointers;
	
	private final Map<Object, cl_mem> buffers;
	
	private final Map<Node<?>, CLKernel> forwardKernels;
	
	private final Map<Node<?>, CLKernel> backwardDiffKernels;
	
	private final Forwarder forwarder;
	
	private final BackwardDiffer backwardDiffer;
	
	private final ForwardGetter forwardGetter;
	
	private final ForwardInitializer forwardInitializer;
	
	private final BackwardDiffGetter backwardDiffGetter;
	
	private final BackwardDiffInitializer backwardDiffInitializer;
	
	public CLProcessor() {
		this(new CLContext());
	}
	
	public CLProcessor(final CLContext context) {
		this.context = context;
		this.pointers = new IdentityHashMap<>();
		this.buffers = new IdentityHashMap<>();
		this.forwardKernels = new IdentityHashMap<>();
		this.backwardDiffKernels = new IdentityHashMap<>();
		this.forwarder = this.new Forwarder();
		this.backwardDiffer = this.new BackwardDiffer();
		this.forwardGetter = this.new ForwardGetter();
		this.forwardInitializer = this.new ForwardInitializer();
		this.backwardDiffGetter = this.new BackwardDiffGetter();
		this.backwardDiffInitializer = this.new BackwardDiffInitializer();
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
		
		for (final Node<?> n : nodes) {
			if (n.hasArguments()) {
				n.accept(this.forwardInitializer).enqueueNDRange(n.getLength());
			}
		}
		
		this.readBuffer(node);
		
		return null;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		if (node.setupDiffs()) {
			final Collection<Node<?>> nodes = node.collectTo(new LinkedHashSet<>()).stream().filter(Node::hasDiffs).collect(toList());
			
			nodes.forEach(n -> this.fill(n.getDiffs(), 0F));
			
			this.fill(node.getDiffs(), 1F);
			
			for (final Node<?> n : nodes) {
				if (n.hasArguments() && n.getDiffs() != null) {
					n.accept(this.backwardDiffInitializer).enqueueNDRange(n.getLength());
				}
			}
			
			for (final Node<?> n : nodes) {
				if (!n.hasArguments() && n.getDiffs() != null) {
					this.readBuffer(n.getDiffs());
				}
			}
		}
		
		return null;
	}
	
	public final CLKernel getForwardKernel(final Node<?> node) {
		return node.accept(this.forwardGetter);
	}
	
	public final CLKernel getBackwardDiffKernel(final Node<?> node) {
		return node.accept(this.backwardDiffGetter);
	}
	
	@Override
	public final void reset() {
		this.buffers.values().forEach(CL::clReleaseMemObject);
		this.buffers.clear();
		
		this.getForwardKernels().values().forEach(CLKernel::release);
		this.getForwardKernels().clear();
		
		this.getBackwardDiffKernels().values().forEach(CLKernel::release);
		this.getBackwardDiffKernels().clear();
	}
	
	final void readBuffer(final Node<?> node) {
		final AbstractNode<?> aNode = (AbstractNode<?>) node;
		
		this.getContext().getDefaultCommandQueue().enqueueReadBuffer(
				this.clBuffer(aNode), Sizeof.cl_float * node.getLength(), this.pointer((AbstractNode<?>) node));
	}
	
	final Map<Node<?>, CLKernel> getForwardKernels() {
		return this.forwardKernels;
	}
	
	final Map<Node<?>, CLKernel> getBackwardDiffKernels() {
		return this.backwardDiffKernels;
	}
	
	final cl_mem clBuffer(final AbstractNode<?> node) {
		return this.buffers.computeIfAbsent(node, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Float.BYTES, node.getLength(),
				this.pointer(node)));
	}
	
	final Pointer pointer(final AbstractNode<?> node) {
		return this.pointers.computeIfAbsent(node, __ -> Pointer.toBuffer(node.getFloatBuffer().position(0)));
	}
	
	final cl_mem clBuffer(final LongBuffer buffer) {
		return this.buffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Long.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final cl_mem clBuffer(final IntBuffer buffer) {
		return this.buffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Integer.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final cl_mem clBuffer(final FloatBuffer buffer) {
		return this.buffers.computeIfAbsent(buffer, __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Float.BYTES, buffer.capacity(),
				this.pointer(buffer.position(0))));
	}
	
	final Pointer pointer(final Buffer buffer) {
		return this.pointers.computeIfAbsent(buffer, __ -> Pointer.toBuffer(buffer));
	}
	
	/**
	 * @author codistmonk (creation 2016-07-18)
	 */
	final class ForwardGetter implements NodeVisitor<CLKernel> {
		
		@Override
		public final CLKernel visit(final MatrixMultiplication node) {
			return getForwardKernels().computeIfAbsent(node, __ -> {
				final Node<?> left = node.getLeft();
				final Node<?> right = node.getRight();
				final int[] leftShape = left.getLengths(new int[2]);
				final int[] rightShape = right.getLengths(new int[2]);
				final int columns = rightShape[1];
				final int stride = leftShape[1];
				final String kernelName = node.getClass().getSimpleName() + getForwardKernels().size();
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float const * const left, ";
				programSource += "__global float const * const right, ";
				programSource += "__global float * const result) {\n";
				programSource += "	int const gid = get_global_id(0);\n";
				programSource += "	int const columns = " + columns + ";\n";
				programSource += "	int const stride = " + stride + ";\n";
				programSource += "	int const r = gid / columns;\n";
				programSource += "	int const c = gid % columns;\n";
				programSource += "	float value = 0.0F;\n";
				programSource += "	for (int k = 0; k < stride; ++k) {\n";
				programSource += "		value += left[k + r * stride] * right[c + k * columns];\n";
				programSource += "	}\n";
				programSource += "	result[gid] = value;\n";
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
				
		private static final long serialVersionUID = -41684012969905022L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-18)
	 */
	final class BackwardDiffGetter implements NodeVisitor<CLKernel> {
		
		@Override
		public final CLKernel visit(final MatrixMultiplication node) {
			return getBackwardDiffKernels().computeIfAbsent(node, __ -> {
				final Node<?> left = node.getLeft();
				final Node<?> right = node.getRight();
				final int[] leftShape = left.getLengths(new int[2]);
				final int[] rightShape = right.getLengths(new int[2]);
				final int columns = rightShape[1];
				final int stride = leftShape[1];
				final String kernelName = node.getClass().getSimpleName() + getBackwardDiffKernels().size();
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float const * const left, ";
				programSource += "__global float * const leftDiffs, ";
				programSource += "__global float const * const right, ";
				programSource += "__global float * const rightDiffs, ";
				programSource += "__global float const * const diffs) {\n";
				programSource += "	int const gid = get_global_id(0);\n";
				programSource += "	int const columns = " + columns + ";\n";
				programSource += "	int const stride = " + stride + ";\n";
				programSource += "	int const r = gid / columns;\n";
				programSource += "	int const c = gid % columns;\n";
				programSource += "	printf(\"gid: %i r: %i c: %i\\n\", gid, r, c);\n";
				programSource += "	float const diff = diffs[gid];\n";
				programSource += "	for (int k = 0; k < stride; ++k) {\n";
				programSource += "		int const leftIndex = k + r * stride;\n";
				programSource += "		int const rightIndex = c + k * columns;\n";
				programSource += "		printf(\"leftIndex: %i rightIndex: %i\\n\", leftIndex, rightIndex);\n";
				programSource += "		if (leftDiffs) {\n";
				programSource += "			printf(\"leftDiffs[leftIndex]: %f\\n\", leftDiffs[leftIndex]);\n";
				programSource += "			leftDiffs[leftIndex] += right[rightIndex] * diff;\n";
				programSource += "			printf(\"leftDiffs[leftIndex]: %f\\n\", leftDiffs[leftIndex]);\n";
				programSource += "		}\n";
				programSource += "		if (rightDiffs) {\n";
				programSource += "			printf(\"rightDiffs[rightIndex]: %f\\n\", rightDiffs[rightIndex]);\n";
				programSource += "			rightDiffs[rightIndex] += left[leftIndex] * diff;\n";
				programSource += "			printf(\"rightDiffs[rightIndex]: %f\\n\", rightDiffs[rightIndex]);\n";
				programSource += "		}\n";
				programSource += "	}\n";
				programSource += "	printf(\"leftDiffs[0]: %f\\n\", leftDiffs[0]);\n";
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
		
		private static final long serialVersionUID = 4021444858946691751L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-18)
	 */
	final class ForwardInitializer implements NodeVisitor<CLKernel> {
		
		@Override
		public final CLKernel visit(final BinaryNode<?> node) {
			final CLKernel result = getForwardKernel(node);
			
			result.setArg(0, clBuffer((AbstractNode<?>) node.getLeft()));
			result.setArg(1, clBuffer((AbstractNode<?>) node.getRight()));
			result.setArg(2, clBuffer(node));
			
			return result;
		}
		
		@Override
		public final CLKernel visit(final UnaryNode<?> node) {
			final CLKernel result = getForwardKernel(node);
			
			result.setArg(0, clBuffer((AbstractNode<?>) node.getArgument()));
			result.setArg(1, clBuffer(node));
			
			return result;
		}
		
		private static final long serialVersionUID = -7362441160666727239L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-18)
	 */
	final class BackwardDiffInitializer implements NodeVisitor<CLKernel> {
		
		@Override
		public final CLKernel visit(final MatrixMultiplication node) {
			final CLKernel result = getBackwardDiffKernel(node);
			
			result.setArg(0, clBuffer((AbstractNode<?>) node.getLeft()));
			result.setArg(1, clBuffer((AbstractNode<?>) node.getLeft().getDiffs()));
			result.setArg(2, clBuffer((AbstractNode<?>) node.getRight()));
			result.setArg(3, clBuffer((AbstractNode<?>) node.getRight().getDiffs()));
			result.setArg(4, clBuffer((AbstractNode<?>) node.getDiffs()));
			
			return result;
		}
		
		private static final long serialVersionUID = -3703844209531018471L;
		
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
	
	static final String stringOf(final int[] ints) {
		return Arrays.toString(ints).replace('[', '{').replace(']', '}');
	}
	
	static final String indexToCartesian(final int n) {
		String result = "";
		
		result += "void indexToCartesian(int const * const lengths, int const index, int * const indices) {\n";
		result += "	for (int i = "+ (n - 1) + ", tmp = index; 0 <= i; --i) {\n";
		result += "		indices[i] = tmp % lengths[i];\n";
		result += "		tmp /= lengths[i];\n";
		result += "	}\n";
		result += "}\n";
		
		return result;
	}
	
	static final String nextCartesian(final int n) {
		String result = "";
		
		result += "bool nextCartesian(int const * const bounds, int * const indices) {\n";
		result += "	for (int i = "+ (n - 1) + "; 0 <= i; --i) {\n";
		result += "		if (++indices[i] <= bounds[2 * i + 1]) {\n";
		result += "			return true;\n";
		result += "		}\n";
		result += "		indices[i] = bounds[2 * i + 0];\n";
		result += "	}\n";
		result += "	return false;\n";
		result += "}\n";
		
		return result;
	}
	
	static final String indexFromCartesian(final int n) {
		String result = "";
		
		result += "int indexFromCartesian(int const * const lengths, int const * const indices) {\n";
		result += "	int result = indices[0];\n";
		result += "	for (int i = 1; i < " + n + "; ++i) {\n";
		result += "		result = indices[i] + lengths[i] * result;\n";
		result += "	}\n";
		result += "	return result;\n";
		result += "}\n";
		
		return result;
	}
	
}
