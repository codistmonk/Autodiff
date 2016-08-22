package autodiff.computing;

import static autodiff.computing.Functions.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.rules.PatternPredicate.rule;
import static java.lang.Math.max;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.swap;
import static org.jocl.CL.CL_MEM_READ_WRITE;
import static org.jocl.CL.CL_MEM_USE_HOST_PTR;
import static org.jocl.CL.setExceptionsEnabled;

import autodiff.cl.CLContext;
import autodiff.cl.CLKernel;
import autodiff.nodes.Computation;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Zipping;
import autodiff.nodes.Computation.ToCLHelper;
import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.proofs.Deduction;
import autodiff.rules.Rules;
import autodiff.rules.PatternPredicate;

import java.io.Serializable;
import java.nio.Buffer;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;
import java.nio.LongBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Pair;
import multij.tools.TicToc;

import org.jocl.CL;
import org.jocl.Pointer;
import org.jocl.Sizeof;
import org.jocl.cl_mem;

/**
 * @author codistmonk (creation 2016-07-17)
 */
public final class CLProcessor implements NodeProcessor {
	
	private final Map<Object, TicToc> timers;
	
	private final Map<Node<?>, List<Node<?>>> forwards;
	
	private final Map<Node<?>, List<Node<?>>> backwards;
	
	private final CLContext context;
	
	private final Map<Object, Pointer> pointers;
	
	private final Map<Object, cl_mem> buffers;
	
	private final Map<Node<?>, CLKernel> forwardKernels;
	
	private final Forwarder forwarder;
	
	private final ForwardGetter forwardGetter;
	
	private final ForwardInitializer forwardInitializer;
	
	public CLProcessor() {
		this(new CLContext());
	}
	
	public CLProcessor(final CLContext context) {
		this.timers = new HashMap<>();
		this.forwards = new HashMap<>();
		this.backwards = new HashMap<>();
		this.context = context;
		this.pointers = new IdentityHashMap<>();
		this.buffers = new IdentityHashMap<>();
		this.forwardKernels = new IdentityHashMap<>();
		this.forwarder = this.new Forwarder();
		this.forwardGetter = this.new ForwardGetter();
		this.forwardInitializer = this.new ForwardInitializer();
	}
	
	@Override
	public final Map<Object, TicToc> getTimers() {
		return this.timers;
	}
	
	@Override
	public final Map<Node<?>, List<Node<?>>> getForwards() {
		return this.forwards;
	}
	
	@Override
	public final Map<Node<?>, List<Node<?>>> getBackwards() {
		return this.backwards;
	}
	
	public final CLContext getContext() {
		return this.context;
	}
	
	@Override
	public final NodeVisitor<Void> getForwarder() {
		return this.forwarder;
	}
	
	@Override
	public final <N extends Node<?>> N fullForward(final N node) {
		NodeProcessor.super.fullForward(node);
		
		this.readBufferNow(node);
		
		return node;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		NodeProcessor.super.fullBackwardDiff(node);
		
		if (node.hasDiffs()) {
			this.readBufferNow(node.getDiffs());
		}
		
		return node;
	}
	
	@Override
	public final void forward(final Iterable<Node<?>> nodes) {
		for (final Node<?> node : nodes) {
			final TicToc timer = getOrCreateTimer(node.getClass().getSimpleName());
			
			timer.tic();
			
			this.writeBuffer(node);
			
			if (node.isComputationNode()) {
				node.accept(this.forwardInitializer).enqueueNDRange(node.getLength());
				
				this.readBuffer(node);
			}
			
			timer.toc();
		}
	}
	
	public final CLKernel getForwardKernel(final Node<?> node) {
		return node.accept(this.forwardGetter);
	}
	
	@Override
	public final void reset() {
		this.buffers.values().forEach(CL::clReleaseMemObject);
		this.buffers.clear();
		
		this.getForwardKernels().values().forEach(CLKernel::release);
		this.getForwardKernels().clear();
	}
	
	final void readBufferNow(final Node<?> node) {
		this.getContext().getDefaultCommandQueue().enqueueReadBuffer(true,
				this.clBuffer(node), Sizeof.cl_float * node.getLength(), this.pointer(node));
	}
	
	final void readBuffer(final Node<?> node) {
		this.getContext().getDefaultCommandQueue().enqueueReadBuffer(false,
				this.clBuffer(node), Sizeof.cl_float * node.getLength(), this.pointer(node));
	}
	
	final void writeBuffer(final Node<?> node) {
		this.getContext().getDefaultCommandQueue().enqueueWriteBuffer(false,
				this.clBuffer(node), Sizeof.cl_float * node.getLength(), this.pointer(node));
	}
	
	final Map<Node<?>, CLKernel> getForwardKernels() {
		return this.forwardKernels;
	}
	
	final cl_mem clBuffer(final Node<?> node) {
		return this.buffers.computeIfAbsent(node.getFloatBuffer(), __ -> getContext().createBuffer(
				CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR, Float.BYTES, node.getLength(),
				this.pointer(node)));
	}
	
	final Pointer pointer(final Node<?> node) {
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
		
		private final Context context = new Context();
		
		@Override
		public final CLKernel visit(final Mapping node) {
			return getForwardKernels().computeIfAbsent(node, __ -> {
				final String functionName = node.getFunctionName();
				final List<Object> forwardDefinition = Functions.getDefinition(functionName, 1);
				final String expression = this.context.newSupplier(forwardDefinition);
				final String kernelName = node.getClass().getSimpleName() + node.getId();
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float const * const argument, ";
				programSource += "__global float * const result) {\n";
				programSource += "	int const gid = get_global_id(0);\n";
				programSource += "	float const x = argument[gid];\n";
				programSource += "	result[gid] += " + expression + ";\n";
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
		
		@Override
		public final CLKernel visit(final Zipping node) {
			return getForwardKernels().computeIfAbsent(node, __ -> {
				final Node<?> left = node.getLeft();
				final Node<?> right = node.getRight();
				final int l = node.getLength();
				final int m = left.getLength();
				final int n = right.getLength();
				final int mm = max(l, max(m, n));
				final String functionName = node.getFunctionName();
				final List<Object> forwardDefinition = Functions.getDefinition(functionName, 2);
				final String expression = this.context.newSupplier(forwardDefinition);
				final String kernelName = node.getClass().getSimpleName() + node.getId();
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float const * const left, ";
				programSource += "__global float const * const right, ";
				programSource += "__global float * const result) {\n";
				programSource += "	int const gid = get_global_id(0);\n";
				programSource += "	for (int i = gid; i < " + mm + "; i += " + l + ") {\n";
				programSource += "		float const x = left[i % " + m + "];\n";
				programSource += "		float const y = right[i % " + n + "];\n";
				programSource += "		result[gid] += " + expression + ";\n";
				programSource += "	}\n";
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
		
		@Override
		public final CLKernel visit(final MatrixMultiplication node) {
			return getForwardKernels().computeIfAbsent(node, __ -> {
				final Node<?> left = node.getLeft();
				final Node<?> right = node.getRight();
				final int[] leftShape = left.getLengths(new int[2]);
				final int[] rightShape = right.getLengths(new int[2]);
				final boolean transposeLeft = node.isTransposeLeft();
				final boolean transposeRight = node.isTransposeRight();
				
				if (transposeLeft) {
					swap(leftShape, 0, 1);
				}
				
				if (transposeRight) {
					swap(rightShape, 0, 1);
				}
				
				final int rows = leftShape[0];
				final int columns = rightShape[1];
				final int stride = leftShape[1];
				final String kernelName = node.getClass().getSimpleName() + node.getId();
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float const * const left, ";
				programSource += "__global float const * const right, ";
				programSource += "__global float * const result) {\n";
				programSource += "	int const gid = get_global_id(0);\n";
				programSource += "	int const rows = " + rows + ";\n";
				programSource += "	int const columns = " + columns + ";\n";
				programSource += "	int const stride = " + stride + ";\n";
				programSource += "	int const r = gid / columns;\n";
				programSource += "	int const c = gid % columns;\n";
				programSource += "	float value = 0.0F;\n";
				programSource += "	for (int k = 0; k < stride; ++k) {\n";
				programSource += "		int const leftIndex = " + (transposeLeft ? "r + k * rows" : "k + r * stride") + ";\n";
				programSource += "		int const rightIndex = " + (transposeRight ? "k + c * stride" : "c + k * columns") + ";\n";
				programSource += "		value += left[leftIndex] * right[rightIndex];\n";
				programSource += "	}\n";
				programSource += "	result[gid] += value;\n";
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
		
		@Override
		public final CLKernel visit(final Computation node) {
			return getForwardKernels().computeIfAbsent(node, __ -> {
				final String kernelName = node.getClass().getSimpleName() + node.getId();
				
				final Deduction clCodeDeduction = Standard.build(new Deduction(node.getBoundForm(), node.getName() + "_to_CL"), new Runnable() {
					
					@Override
					public final void run() {
						final Object boundForm = proposition(-1);
						final Object valuesExpression = left(middle(right(boundForm)));
						
						new ToCLHelper().compute($("to_CL", valuesExpression));
					}
					
				}, 1);
				
				String programSource = "";
				
				programSource += "__kernel void " + kernelName + "(";
				programSource += "__global float * const result) {\n";
				programSource += Computation.deepJoin("",
						(Iterable<?>) right(clCodeDeduction.getProposition(clCodeDeduction.getPropositionName(-1))));
				programSource += "}\n";
				
				return getContext().createAndBuildProgram(programSource).createKernel(kernelName);
			});
		}
		
		private static final long serialVersionUID = -41684012969905022L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-18)
	 */
	final class ForwardInitializer implements NodeVisitor<CLKernel> {
		
		@Override
		public final CLKernel visit(final Node<?> node) {
			final CLKernel result = getForwardKernel(node);
			final int n = node.getArguments().size();
			
			for (int i = 0; i < n; ++i) {
				result.setArg(i, clBuffer(node.getArguments().get(i)));
			}
			
			result.setArg(n, clBuffer(node));
			
			return result;
		}
		
		private static final long serialVersionUID = -7362441160666727239L;
		
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
	
	/**
	 * @author codistmonk (creation 2016-08-02)
	 */
	public static final class Context implements Serializable {
		
		private final Rules<Object, String> rules = new Rules<>();
		
		{
			for (final List<Object> definition : Functions.getDefinitions().values()) {
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					final autodiff.rules.Variable z = new autodiff.rules.Variable();
					final List<Object> function1DefinitionPattern = $$(FORALL, $$(x), IN, R, $$(y, "=", z));
					final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
					
					if (autodiff.rules.Variable.match(function1DefinitionPattern, definition, mapping)
							&& !mapping.get(y).equals(mapping.get(z))) {
						final Map<Object, Object> m_ = new HashMap<>();
						
						m_.put(mapping.get(x), x);
						
						final Object y_ = autodiff.rules.Variable.rewrite(mapping.get(y), m_);
						final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
						
						this.rules.add(new PatternPredicate(y_), (__, m) -> this.rules.applyTo(z_, m));
					}
				}
				
				{
					final autodiff.rules.Variable x0 = new autodiff.rules.Variable();
					final autodiff.rules.Variable x1 = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					final autodiff.rules.Variable z = new autodiff.rules.Variable();
					final List<Object> function2DefinitionPattern = $$(FORALL, $$(x0, x1), IN, R, $$(y, "=", z));
					final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
					
					if (autodiff.rules.Variable.match(function2DefinitionPattern, definition, mapping)
							&& !mapping.get(y).equals(mapping.get(z))) {
						final Map<Object, Object> m_ = new HashMap<>();
						
						m_.put(mapping.get(x0), x0);
						m_.put(mapping.get(x1), x1);
						
						final Object y_ = autodiff.rules.Variable.rewrite(mapping.get(y), m_);
						final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
						
						this.rules.add(new PatternPredicate(y_), (__, m) -> this.rules.applyTo(z_, m));
					}
				}
			}
			
			{
				this.rules.add((expr, __) -> {
					final List<?> list = cast(List.class, expr);
					
					return list != null && 2 <= list.size() && CASES.equals(list.get(0));
				}, (expr, m) -> {
					final List<?> list = (List<?>) expr;
					final List<Pair<String, String>> conditionAndResults = new ArrayList<>();
					
					for (int i = 1; i < list.size(); ++i) {
						final List<?> caseElement = (List<?>) list.get(i);
						
						if (caseElement.size() == 3) {
							if (!IF.equals(caseElement.get(1))) {
								throw new IllegalArgumentException();
							}
							
							conditionAndResults.add(new Pair<>(
									this.rules.applyTo(caseElement.get(2), m), this.rules.applyTo(caseElement.get(0), m)));
						} else {
							if (caseElement.size() != 2 || !OTHERWISE.equals(caseElement.get(1))) {
								throw new IllegalArgumentException();
							}
							
							conditionAndResults.add(new Pair<>(null, this.rules.applyTo(caseElement.get(0), m)));
						}
					}
					
					String result = null;
					
					for (int i = conditionAndResults.size() - 1; 0 <= i; --i) {
						final Pair<String, String> conditionAndResult = conditionAndResults.get(i);
						
						if (conditionAndResult.getFirst() == null) {
							result = conditionAndResult.getSecond();
						} else {
							result = "(" + conditionAndResult.getFirst() + " ? " + conditionAndResult.getSecond() + " : " + result + ")";
						}
					}
					
					return result;
				});
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(ABS, x), (__, m) -> {
					return prefix("abs", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(SQRT, x), (__, m) -> {
					return prefix("sqrt", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(EXP, x), (__, m) -> {
					return prefix("exp", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$("-", x), (__, m) -> {
					return prefix("-", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(LN, x), (__, m) -> {
					return prefix("log", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(SIN, x), (__, m) -> {
					return prefix("sin", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(COS, x), (__, m) -> {
					return prefix("cos", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(ROUND, x), (__, m) -> {
					return prefix("round", x, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "+", y), (__, m) -> {
					return infix("+", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "-", y), (__, m) -> {
					return infix("-", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "*", y), (__, m) -> {
					return infix("*", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "/", y), (__, m) -> {
					return infix("/", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "=", y), (__, m) -> {
					return infix("==", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "!=", y), (__, m) -> {
					return infix("!=", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "<", y), (__, m) -> {
					return infix("<", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, "<=", y), (__, m) -> {
					return infix("<=", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, ">", y), (__, m) -> {
					return infix(">", x, y, m);
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($$(x, ">=", y), (__, m) -> {
					return infix(">=", x, y, m);
				}));
			}
			
			this.rules.add((object, __) -> object instanceof autodiff.rules.Variable, (name, m) -> {
				final Object value = DefaultProcessor.Context.transitiveGet(m, name);
				
				if (value instanceof String) {
					return (String) value;
				}
				
				return this.rules.applyTo(value, m);
			});
			
			this.rules.add((object, __) -> object instanceof Number, (x, __) -> x.toString());
		}
		
		final String prefix(final String op, final autodiff.rules.Variable x, final Map<autodiff.rules.Variable, Object> m) {
			return op + "(" + this.rules.applyTo(m.get(x), m) + ")";
		}
		
		final String infix(final String op, final autodiff.rules.Variable x, final autodiff.rules.Variable y, final Map<autodiff.rules.Variable, Object> m) {
			return "(" + this.rules.applyTo(m.get(x), m) + op + this.rules.applyTo(m.get(y), m) + ")";
		}
		
		public final Rules<Object, String> getRules() {
			return this.rules;
		}
		
		public final Context reset() {
			// TODO
			return this;
		}
		
		public final String newSupplier(final Object definition) {
			this.reset();
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				final autodiff.rules.Variable z = new autodiff.rules.Variable();
				final List<Object> function1DefinitionPattern = $$(FORALL, $$(x), IN, R, $$(y, "=", z));
				final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
				
				if (autodiff.rules.Variable.match(function1DefinitionPattern, definition, mapping)) {
//					final Variable variable = new Variable();
					
//					if (this.variables.put(x, variable) != null) {
//						throw new IllegalStateException();
//					}
//					
//					if (this.inputs.isEmpty()) {
//						this.inputs.add(variable);
//					}
					
					final Map<Object, Object> m_ = new HashMap<>();
					m_.put(mapping.get(x), x);
					final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
					
//					mapping.put(x, variable);
					
					return this.rules.applyTo(z_, mapping);
				}
			}
			
			{
				final autodiff.rules.Variable x0 = new autodiff.rules.Variable();
				final autodiff.rules.Variable x1 = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				final autodiff.rules.Variable z = new autodiff.rules.Variable();
				final List<Object> function2DefinitionPattern = $$(FORALL, $$(x0, x1), IN, R, $$(y, "=", z));
				final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
				
				if (autodiff.rules.Variable.match(function2DefinitionPattern, definition, mapping)) {
//					final Variable variable0 = new Variable();
//					
//					if (this.variables.put(x0, variable0) != null) {
//						throw new IllegalStateException();
//					}
//					
//					final Variable variable1 = new Variable();
//					
//					if (this.variables.put(x1, variable1) != null) {
//						throw new IllegalStateException();
//					}
//					
//					if (this.inputs.isEmpty()) {
//						this.inputs.add(variable0);
//						this.inputs.add(variable1);
//					}
					
					final Map<Object, Object> m_ = new HashMap<>();
					m_.put(mapping.get(x0), x0);
					m_.put(mapping.get(x1), x1);
					final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
					
//					mapping.put(x0, variable0);
//					mapping.put(x1, variable1);
					
					return this.rules.applyTo(z_, mapping);
				}
			}
			
			throw new IllegalArgumentException("" + definition);
		}
		
		private static final long serialVersionUID = -6674979862323358009L;
		
	}
	
}
