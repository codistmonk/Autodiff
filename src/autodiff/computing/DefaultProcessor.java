package autodiff.computing;

import static autodiff.computing.Functions.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.v;
import static autodiff.reasoning.tactics.Stack.proposition;
import static multij.rules.PatternPredicate.matchWith;
import static java.lang.Math.*;
import static multij.tools.Tools.*;

import autodiff.nodes.Computation;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Zipping;
import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.Sequences;
import autodiff.reasoning.deductions.ToJavaCode;
import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.expressions.Expressions;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Stack;

import java.io.Serializable;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import multij.rules.Rules;
import multij.rules.PatternPredicate;
import multij.tools.Pair;
import multij.tools.TicToc;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class DefaultProcessor implements NodeProcessor {
	
	private final Map<Object, TicToc> timers = new HashMap<>();
	
	private final Map<Node<?>, Object> computationCodes = new HashMap<>();
	
	private final Map<Node<?>, List<Node<?>>> forwards = new HashMap<>();
	
	private final Map<Node<?>, List<Node<?>>> backwards = new HashMap<>();
	
	private final Forwarder forwarder = this.new Forwarder();
	
	@Override
	public final Map<Object, TicToc> getTimers() {
		return this.timers;
	}
	
	public final Map<Node<?>, Object> getComputationCodes() {
		return this.computationCodes;
	}
	
	@Override
	public final Map<Node<?>, List<Node<?>>> getForwards() {
		return this.forwards;
	}
	
	@Override
	public final Map<Node<?>, List<Node<?>>> getBackwards() {
		return this.backwards;
	}
	
	@Override
	public final Forwarder getForwarder() {
		return this.forwarder;
	}
	
	private static final long serialVersionUID = -5998082453824765555L;
	
	public static final DefaultProcessor INSTANCE = new DefaultProcessor();
	
	/**
	 * @author codistmonk (creation 2016-07-11)
	 */
	public final class Forwarder implements NodeVisitor<Void> {
		
		private final Context context = new Context();
		
		@Override
		public final Void visit(final MatrixMultiplication node) {
			final TicToc timer = getOrCreateTimer("MatrixMultiplication");
			
			timer.tic();
			
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
			
			for (int r = 0; r < rows; ++r) {
				for (int c = 0; c < columns; ++c) {
					float value = 0F;
					
					for (int k = 0; k < stride; ++k) {
						final int leftIndex = transposeLeft ? r + k * rows : k + r * stride;
						final int rightIndex = transposeRight ? k + c * stride : c + k * columns;
						final float leftValue = left.get(leftIndex);
						final float rightValue = right.get(rightIndex);
						
						value += leftValue * rightValue;
					}
					
					node.add(c + r * columns, value);
				}
			}
			
			timer.toc();
			
			return null;
		}
		
		@Override
		public final Void visit(final Mapping node) {
			final TicToc timer = getOrCreateTimer("Mapping");
			
			timer.tic();
			
			final Node<?> argument = node.getArgument();
			final int n = node.getLength();
			final String functionName = node.getFunctionName();
			final List<Object> forwardDefinition = Functions.getDefinition(functionName, 1);
			final FloatSupplier forward = this.context.newSupplier(forwardDefinition);
			
			for (int i = 0; i < n; ++i) {
				this.context.getInputs().get(0).set(argument.get(i));
				
				final float value = forward.get();
				
				node.add(i, value);
			}
			
			timer.toc();
			
			return null;
		}
		
		@Override
		public final Void visit(final Zipping node) {
			final TicToc timer = getOrCreateTimer("Zipping");
			
			timer.tic();
			
			final Node<?> left = node.getLeft();
			final Node<?> right = node.getRight();
			final int l = node.getLength();
			final int m = left.getLength();
			final int n = right.getLength();
			final int mm = max(l, max(m, n));
			final String functionName = node.getFunctionName();
			final List<Object> forwardDefinition = Functions.getDefinition(functionName, 2);
			final FloatSupplier forward = this.context.newSupplier(forwardDefinition);
			
			for (int i = 0; i < mm; ++i) {
				final float leftValue = left.get(i % m);
				final float rightValue = right.get(i % n);
				
				this.context.getInputs().get(0).set(leftValue);
				this.context.getInputs().get(1).set(rightValue);
				
				final float value = forward.get();
				
				node.add(i % l, value);
			}
			
			timer.toc();
			
			return null;
		}
		
		@Override
		public final Void visit(final Computation node) {
			final TicToc timer = getOrCreateTimer("ComputationNode");
			
			timer.tic();
			
			final Object javaCode = getComputationCodes().computeIfAbsent(node, __ -> {
				final Deduction javaCodeDeduction = Basics.build(new Deduction(node.getBoundForm(), node.getName() + "_to_java"), new Runnable() {
					
					@Override
					public final void run() {
						final Object boundForm = proposition(-1);
						final Object valuesExpression = left(middle(right(boundForm)));
						
						Stack.bind("identity", $$("to_java", valuesExpression));
						ToJavaCode.computeToJava(proposition(-1));
						Stack.abort();
					}
					
				}, new Simple(1));
				
				return right(javaCodeDeduction.getProposition(javaCodeDeduction.getPropositionName(-1)));
			});
			
			{
				final JavaCodeContext context = new JavaCodeContext();
				
				context.setBuffer("result", node.getFloatBuffer());
				
				context.run(javaCode);
			}
			
			timer.toc();
			
			return null;
		}
		
		private static final long serialVersionUID = -8842155630294708599L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-16)
	 */
	public static final class JavaCodeContext implements Serializable {
		
		private final Map<String, FloatBuffer> buffers = new LinkedHashMap<>();
		
		private final Interpreter interpreter = this.new Interpreter();
		
		public final Object run(final Object program) {
			return this.interpreter.apply(program);
		}
		
		public final void repeat(final Number n, final String counterName, final Number counterIndex, final Runnable instructions) {
			final String deltaName = this.buffers.size() + ":delta";
			
			this.allocate(deltaName, 1);
			this.write(deltaName, 0, 1);
			
			for (this.write(counterName, counterIndex, 0);
					this.read(counterName, counterIndex) < n.intValue();
					this.addTo(counterName, counterIndex, deltaName, 0)) {
				instructions.run();
			}
		}
		
		public final void allocate(final String name, final Number n) {
			this.buffers.put(name,
					ByteBuffer.allocateDirect(n.intValue() * Float.BYTES).order(ByteOrder.nativeOrder()).asFloatBuffer());
		}
		
		public final void write(final String targetName, final Number index, final Number value) {
			this.getBuffer(targetName).put(index.intValue(), value.floatValue());
		}
		
		public final float read(final String sourceName, final Number index) {
			return this.getBuffer(sourceName).get(index.intValue());
		}
		
		public final void addTo(final String targetName, final Number targetIndex, final String sourceName, final Number sourceIndex) {
			this.addTo(targetName, targetIndex, this.read(sourceName, sourceIndex));
		}
		
		public final void addTo(final String targetName, final Number targetIndex, final Number value) {
			this.write(targetName, targetIndex,
					this.read(targetName, targetIndex) + value.floatValue());
		}
		
		public final float floor(final String sourceName, final Number index) {
			return this.floor(this.read(sourceName, index));
		}
		
		public final float floor(final Number value) {
			return (float) Math.floor(value.floatValue());
		}
		
		public final FloatBuffer getBuffer(final String name) {
			return this.buffers.get(name);
		}
		
		public final void setBuffer(final String name, final FloatBuffer buffer) {
			this.buffers.put(name, buffer);
		}
		
		public final Object ifThenElse(final boolean condition, final Supplier<Object> thenWhat, final Supplier<Object> whatElse) {
			return condition ? thenWhat.get() : whatElse.get();
		}
		
		/**
		 * @author codistmonk (creation 2016-08-16)
		 */
		public final class Interpreter implements ExpressionRewriter {
			
			private final Rules<Object, Object> rules = new Rules<>();
			
			{
				{
					final multij.rules.Variable s = v("s");
					
					this.rules.add(matchWith(Expressions.$("\"", s, "\""), (__, m) -> (Object) m.get(s).toString()));
				}
				
				{
					final multij.rules.Variable p = v("p");
					
					this.rules.add(matchWith(Expressions.$("()->{", p, "}"), (__, m) -> new Runnable() {
						
						private final Object _p = m.get(p);
						
						@Override
						public final void run() {
							Interpreter.this.apply(this._p);
						}
						
					}));
				}
				
				{
					final multij.rules.Variable vf = v("f");
					final multij.rules.Variable vx = v("x");
					
					this.rules.add(matchWith(Expressions.$(vf, "(", vx, ")"), (__, m) -> {
						final Object _f = vf.get();
						final Object _x = vx.get();
						final List<Object> arguments = Sequences.flattenSequence(",", this.apply(_x));
						
						return invoke(JavaCodeContext.this, _f.toString(), arguments.toArray());
					}));
				}
				
				{
					final multij.rules.Variable vx = v("x");
					final multij.rules.Variable vc = v("c");
					final multij.rules.Variable vy = v("y");
					
					this.rules.add(matchWith(Expressions.$(vc, "?", vx, ":", vy), (__, m) -> {
						final Object _x = vx.get();
						final Object _c = vc.get();
						final Object _y = vy.get();
						
						return JavaCodeContext.this.ifThenElse(this.b(this.apply(_c)),
								() -> this.apply(_x), () -> this.apply(_y));
					}));
				}
				
				{
					final multij.rules.Variable vx = v("x");
					final multij.rules.Variable vy = v("y");
					
					this.rules.add(matchWith(Expressions.$(vx, "+", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) + this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "-", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) - this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "*", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) * this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "/", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) / this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "%", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) % this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "<", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) < this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, ">", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) > this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$(vx, "==", vy), (e, m) -> {
						final Object x = vx.get();
						final Object y = vy.get();
						
						return this.f(x) == this.f(y);
					}));
					
					this.rules.add(matchWith(Expressions.$("(", vx, ")"), (e, m) -> {
						return this.apply(vx.get());
					}));
				}
				
				{
					this.rules.add(matchWith(new multij.rules.Variable("*"), (e, __) -> ExpressionRewriter.super.visit((List<?>) e)));
				}
			}
			
			public final float f(final Object object) {
				return JavaCodeContext.f(this.apply(object));
			}
			
			public final boolean b(final Object object) {
				return JavaCodeContext.b(this.apply(object));
			}
			
			@Override
			public final Object visit(final List<?> expression) {
				return this.rules.applyTo(expression);
			}
			
			private static final long serialVersionUID = -6614888521968958004L;
			
		}
		
		private static final long serialVersionUID = -7818200319668460156L;
		
		public static final float f(final Object object) {
			return ((Number) object).floatValue();
		}
		
		public static final boolean b(final Object object) {
			return (Boolean) object;
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Context implements Serializable {
		
		private final Rules<Object, FloatSupplier> rules = new Rules<>();
		
		private final List<Variable> inputs = new ArrayList<>();
		
		private final Map<Object, Variable> variables = new HashMap<>();
		
		{
			for (final List<Object> definition : Functions.getDefinitions().values()) {
				{
					final multij.rules.Variable x = new multij.rules.Variable();
					final multij.rules.Variable y = new multij.rules.Variable();
					final multij.rules.Variable z = new multij.rules.Variable();
					final List<Object> function1DefinitionPattern = $$(FORALL, $$(x), IN, R, $$(y, "=", z));
					final Map<multij.rules.Variable, Object> mapping = new HashMap<>();
					
					if (multij.rules.Variable.match(function1DefinitionPattern, definition, mapping)
							&& !mapping.get(y).equals(mapping.get(z))) {
						final Map<Object, Object> m_ = new HashMap<>();
						
						m_.put(mapping.get(x), x);
						
						final Object y_ = multij.rules.Variable.rewrite(mapping.get(y), m_);
						final Object z_ = multij.rules.Variable.rewrite(mapping.get(z), m_);
						
						this.rules.add(new PatternPredicate(y_), (__, m) -> this.rules.applyTo(z_, m));
					}
				}
				
				{
					final multij.rules.Variable x0 = new multij.rules.Variable();
					final multij.rules.Variable x1 = new multij.rules.Variable();
					final multij.rules.Variable y = new multij.rules.Variable();
					final multij.rules.Variable z = new multij.rules.Variable();
					final List<Object> function2DefinitionPattern = $$(FORALL, $$(x0, x1), IN, R, $$(y, "=", z));
					final Map<multij.rules.Variable, Object> mapping = new HashMap<>();
					
					if (multij.rules.Variable.match(function2DefinitionPattern, definition, mapping)
							&& !mapping.get(y).equals(mapping.get(z))) {
						final Map<Object, Object> m_ = new HashMap<>();
						
						m_.put(mapping.get(x0), x0);
						m_.put(mapping.get(x1), x1);
						
						final Object y_ = multij.rules.Variable.rewrite(mapping.get(y), m_);
						final Object z_ = multij.rules.Variable.rewrite(mapping.get(z), m_);
						
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
					final List<Pair<FloatSupplier, FloatSupplier>> conditionAndResults = new ArrayList<>();
					
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
					
					FloatSupplier result = null;
					
					for (int i = conditionAndResults.size() - 1; 0 <= i; --i) {
						final Pair<FloatSupplier, FloatSupplier> conditionAndResult = conditionAndResults.get(i);
						
						if (conditionAndResult.getFirst() == null) {
							result = conditionAndResult.getSecond();
						} else {
							result = new IfThenElse(conditionAndResult.getFirst(), conditionAndResult.getSecond(), result);
						}
					}
					
					return result;
				});
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(ABS, x), (__, m) -> {
					return new Abs(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(SQRT, x), (__, m) -> {
					return new Sqrt(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(EXP, x), (__, m) -> {
					return new Exp(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$("-", x), (__, m) -> {
					return new Neg(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(LN, x), (__, m) -> {
					return new Ln(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(SIN, x), (__, m) -> {
					return new Sin(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(COS, x), (__, m) -> {
					return new Cos(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(ROUND, x), (__, m) -> {
					return new Round(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "+", y), (__, m) -> {
					return new Plus(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "-", y), (__, m) -> {
					return new Minus(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "*", y), (__, m) -> {
					return new Times(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "/", y), (__, m) -> {
					return new Div(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "=", y), (__, m) -> {
					return new Equal(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "!=", y), (__, m) -> {
					return new NotEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "<", y), (__, m) -> {
					return new Less(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, "<=", y), (__, m) -> {
					return new LessOrEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, ">", y), (__, m) -> {
					return new Greater(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				
				this.rules.add(matchWith($$(x, ">=", y), (__, m) -> {
					return new GreaterOrEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			this.rules.add((object, __) -> object instanceof multij.rules.Variable, (name, m) -> {
				final Object value = transitiveGet(m, name);
				
				if (value instanceof FloatSupplier) {
					return (FloatSupplier) value;
				}
				
				return this.rules.applyTo(value, m);
			});
			
			this.rules.add((object, __) -> object instanceof Number, (x, __) -> new Constant(((Number) x).floatValue()));
		}
		
		public final Rules<Object, FloatSupplier> getRules() {
			return this.rules;
		}
		
		public final List<Variable> getInputs() {
			return this.inputs;
		}
		
		public final Map<Object, Variable> getVariables() {
			return this.variables;
		}
		
		public final Context reset() {
			this.getInputs().clear();
			this.getVariables().clear();
			
			return this;
		}
		
		public final FloatSupplier newSupplier(final Object definition) {
			this.reset();
			
			{
				final multij.rules.Variable x = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				final multij.rules.Variable z = new multij.rules.Variable();
				final List<Object> function1DefinitionPattern = $$(FORALL, $$(x), IN, R, $$(y, "=", z));
				final Map<multij.rules.Variable, Object> mapping = new HashMap<>();
				
				if (multij.rules.Variable.match(function1DefinitionPattern, definition, mapping)) {
					final Variable variable = new Variable();
					
					if (this.variables.put(x, variable) != null) {
						throw new IllegalStateException();
					}
					
					if (this.inputs.isEmpty()) {
						this.inputs.add(variable);
					}
					
					final Map<Object, Object> m_ = new HashMap<>();
					m_.put(mapping.get(x), x);
					final Object z_ = multij.rules.Variable.rewrite(mapping.get(z), m_);
					
					mapping.put(x, variable);
					
					return this.rules.applyTo(z_, mapping);
				}
			}
			
			{
				final multij.rules.Variable x0 = new multij.rules.Variable();
				final multij.rules.Variable x1 = new multij.rules.Variable();
				final multij.rules.Variable y = new multij.rules.Variable();
				final multij.rules.Variable z = new multij.rules.Variable();
				final List<Object> function2DefinitionPattern = $$(FORALL, $$(x0, x1), IN, R, $$(y, "=", z));
				final Map<multij.rules.Variable, Object> mapping = new HashMap<>();
				
				if (multij.rules.Variable.match(function2DefinitionPattern, definition, mapping)) {
					final Variable variable0 = new Variable();
					
					if (this.variables.put(x0, variable0) != null) {
						throw new IllegalStateException();
					}
					
					final Variable variable1 = new Variable();
					
					if (this.variables.put(x1, variable1) != null) {
						throw new IllegalStateException();
					}
					
					if (this.inputs.isEmpty()) {
						this.inputs.add(variable0);
						this.inputs.add(variable1);
					}
					
					final Map<Object, Object> m_ = new HashMap<>();
					m_.put(mapping.get(x0), x0);
					m_.put(mapping.get(x1), x1);
					final Object z_ = multij.rules.Variable.rewrite(mapping.get(z), m_);
					
					mapping.put(x0, variable0);
					mapping.put(x1, variable1);
					
					return this.rules.applyTo(z_, mapping);
				}
			}
			
			throw new IllegalArgumentException("" + definition);
		}
		
		private static final long serialVersionUID = 5823521748135325332L;
		
		@SuppressWarnings("unchecked")
		public static final <T> T transitiveGet(final Map<?, ?> map, final Object key) {
			Object result = key;
			Object next = map.get(result);
			
			while (next != null) {
				result = next;
				next = map.get(result);
			}
			
			return (T) result;
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static abstract interface FloatSupplier extends Serializable {
		
		public abstract float get();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Constant implements FloatSupplier {
		
		private final float value;
		
		public Constant(final float value) {
			this.value = value;
		}
		
		@Override
		public final float get() {
			return this.value;
		}
		
		@Override
		public final String toString() {
			return "" + this.get(); 
		}
		
		private static final long serialVersionUID = 1017034235821362234L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Variable implements FloatSupplier {
		
		private float value;
		
		@Override
		public final float get() {
			return this.value;
		}
		
		public final Variable set(final float value) {
			this.value = value;
			
			return this;
		}
		
		@Override
		public final String toString() {
			return "(" + this.get() + ")"; 
		}
		
		private static final long serialVersionUID = -654537403002828566L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static abstract class Unary implements FloatSupplier {
		
		private final FloatSupplier argument;
		
		protected Unary(final FloatSupplier argument) {
			this.argument = argument;
		}
		
		@Override
		public final String toString() {
			return "(" + this.getClass().getSimpleName() + " " + this.getArgument() + ")"; 
		}
		
		protected final FloatSupplier getArgument() {
			return this.argument;
		}
		
		private static final long serialVersionUID = 5214749986194295496L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static abstract class Binary implements FloatSupplier {
		
		private final FloatSupplier left;
		
		private final FloatSupplier right;
		
		protected Binary(final FloatSupplier left, final FloatSupplier right) {
			this.left = left;
			this.right = right;
		}
		
		public final FloatSupplier getLeft() {
			return this.left;
		}
		
		public final FloatSupplier getRight() {
			return this.right;
		}
		
		@Override
		public final String toString() {
			return "(" + this.getLeft() + " " + this.getClass().getSimpleName() + " " + this.getRight() + ")"; 
		}
		
		private static final long serialVersionUID = 1573188791368623911L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class IfThenElse implements FloatSupplier {
		
		private final FloatSupplier condition;
		
		private final FloatSupplier resultIfConditionNot0;
		
		private final FloatSupplier resultElse;
		
		public IfThenElse(final FloatSupplier condition, final FloatSupplier resultIfConditionNot0, final FloatSupplier resultElse) {
			this.condition = condition;
			this.resultIfConditionNot0 = resultIfConditionNot0;
			this.resultElse = resultElse;
		}
		
		public final FloatSupplier getCondition() {
			return this.condition;
		}
		
		public final FloatSupplier getResultIfConditionNot0() {
			return this.resultIfConditionNot0;
		}
		
		public final FloatSupplier getResultElse() {
			return this.resultElse;
		}
		
		@Override
		public final float get() {
			return this.getCondition().get() != 0F ? this.getResultIfConditionNot0().get() : this.getResultElse().get();
		}
		
		@Override
		public final String toString() {
			return "(" + this.getCondition() + " ? " + this.getResultIfConditionNot0() + " : " + this.getResultElse() + ")"; 
		}
		
		private static final long serialVersionUID = -1559004754514756270L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Abs extends Unary {
		
		public Abs(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return abs(x);
		}
		
		private static final long serialVersionUID = 4772288207244596906L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Sqrt extends Unary {
		
		public Sqrt(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return (float) sqrt(x);
		}
		
		private static final long serialVersionUID = -2733073584435575418L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Neg extends Unary {
		
		public Neg(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return -x;
		}
		
		private static final long serialVersionUID = -8694093573365716807L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Exp extends Unary {
		
		public Exp(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return (float) exp(x);
		}
		
		private static final long serialVersionUID = 5639205049295267343L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Ln extends Unary {
		
		public Ln(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return (float) log(x);
		}
		
		private static final long serialVersionUID = -6123018025469779034L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-14)
	 */
	public static final class Sin extends Unary {
		
		public Sin(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return (float) sin(x);
		}
		
		private static final long serialVersionUID = 6014483055967223083L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-14)
	 */
	public static final class Cos extends Unary {
		
		public Cos(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return (float) cos(x);
		}
		
		private static final long serialVersionUID = 1097749855046748151L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-09)
	 */
	public static final class Round extends Unary {
		
		public Round(final FloatSupplier source) {
			super(source);
		}
		
		@Override
		public final float get() {
			return forward(this.getArgument().get());
		}
		
		public static final float forward(final float x) {
			return round(x);
		}
		
		private static final long serialVersionUID = 1097749855046748151L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Plus extends Binary {
		
		public Plus(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x + y;
		}
		
		private static final long serialVersionUID = 170971425719464875L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Minus extends Binary {
		
		public Minus(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x - y;
		}
		
		private static final long serialVersionUID = -454788582776666492L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Times extends Binary {
		
		public Times(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x * y;
		}
		
		private static final long serialVersionUID = 6130248205204905853L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Div extends Binary {
		
		public Div(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
//			if (x == y) {
//				return 1F;
//			}
			
			return x / y;
		}
		
		private static final long serialVersionUID = -8379848103818534300L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Equal extends Binary {
		
		public Equal(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x == y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = 5253789665470122119L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class NotEqual extends Binary {
		
		public NotEqual(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x != y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = 213031248648498288L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Less extends Binary {
		
		public Less(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x < y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = 7113362991557989862L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class LessOrEqual extends Binary {
		
		public LessOrEqual(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x <= y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = 7528620124735745742L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Greater extends Binary {
		
		public Greater(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x > y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = -1705577150600444376L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class GreaterOrEqual extends Binary {
		
		public GreaterOrEqual(final FloatSupplier left, final FloatSupplier right) {
			super(left, right);
		}
		
		@Override
		public final float get() {
			return forward(this.getLeft().get(), this.getRight().get());
		}
		
		public static final float forward(final float x, final float y) {
			return x >= y ? 1F : 0F;
		}
		
		private static final long serialVersionUID = -5380457151343076928L;
		
	}
	
}
