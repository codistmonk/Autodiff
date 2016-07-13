package autodiff.processors;

import static autodiff.nodes.Mapping.*;
import static autodiff.rules.PatternPredicate.rule;
import static java.lang.Math.*;
import static java.util.Collections.reverse;
import static multij.tools.Tools.debugPrint;

import autodiff.nodes.Convolution2D;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node;
import autodiff.nodes.Node2D;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Selection;
import autodiff.nodes.Sum;
import autodiff.rules.Disjunction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class DefaultProcessor implements NodeProcessor {
	
	@Override
	public final Forwarder getForwarder() {
		return Forwarder.INSTANCE;
	}
	
	@Override
	public final BackwardDiffer getBackwardDiffer() {
		return BackwardDiffer.INSTANCE;
	}
	
	@Override
	public final <N extends Node<?>> N fill(final N node, final float value) {
		final int n = node.getLength();
		
		for (int i = 0; i < n; ++i) {
			node.set(i, value);
		}
		
		return node;
	}
	
	@Override
	public final <N extends Node<?>> N fullForward(final N node) {
		final List<Node<?>> nodes = new ArrayList<>(node.collectTo(new LinkedHashSet<>()));
		
		reverse(nodes);
		
		nodes.stream().filter(n -> !n.getArguments().isEmpty()).forEach(n -> this.fill(n, 0F));
		nodes.forEach(n -> n.accept(this.getForwarder()));
		
		return node;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		if (node.setupDiffs()) {
			this.fill(node.getDiffs(), 1F);
			
			node.collectTo(new LinkedHashSet<>()).forEach(n -> n.accept(this.getBackwardDiffer()));
		}
		
		return node;
	}
	
	private static final long serialVersionUID = -5998082453824765555L;
	
	public static final DefaultProcessor INSTANCE = new DefaultProcessor();
	
	/**
	 * @author codistmonk (creation 2016-07-11)
	 */
	public static final class Forwarder implements NodeVisitor<Void> {
		
		private final Context context = new Context();
		
		@Override
		public final Void visit(final Selection node) {
			final int m = node.getVectors().getLength();
			final int n = node.getIndices().getLength();
			final int stride = m / n;
			
			for (int i = 0, j = 0; i < m; i += stride, ++j) {
				node.set(j, node.getVectors().get(i + (int) node.getIndices().get(j)));
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final MatrixMultiplication node) {
			final Node<?> left = node.getLeft();
			final Node<?> right = node.getRight();
			final int[] leftShape = left.getLengths(new int[2]);
			final int[] rightShape = right.getLengths(new int[2]);
			final int rows = leftShape[0];
			final int columns = rightShape[1];
			final int stride = leftShape[1];
			
			for (int r = 0; r < rows; ++r) {
				for (int c = 0; c < columns; ++c) {
					float value = 0F;
					
					for (int k = 0; k < stride; ++k) {
						value += left.get(k + r * stride) * right.get(c + k * columns);
					}
					
					node.set(c + r * columns, value);
				}
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final Sum node) {
			final int n = node.getArgument().getLength();
			final int stride = node.getStride();
			
			for (int i = 0, j = 0; i < n; i += stride, ++j) {
				float value = 0F;
				
				for (int k = 0; k < stride; ++k) {
					value += node.getArgument().get(i + k);
				}
				
				node.set(j, value);
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final Convolution2D node) {
			final Node<?> inputs = node.getInputs();
			final Node<?> kernel = node.getKernel();
			final int[] inputsShape = inputs.getShape();
			final int[] kernelShape = kernel.getShape();
			final int inputWidth = inputsShape[inputsShape.length - 1];
			final int inputHeight = inputsShape[inputsShape.length - 2];
			final int[] offsets = node.getOffsets();
			final int leftOffset = offsets[Node2D.LEFT];
			final int rightOffset = offsets[Node2D.RIGHT];
			final int topOffset = offsets[Node2D.TOP];
			final int bottomOffset = offsets[Node2D.BOTTOM];
			final int[] strides = node.getStrides();
			final int strideX = strides[Node2D.HORIZONTAL];
			final int strideY = strides[Node2D.VERTICAL];
			final int kernelWidth = kernelShape[kernelShape.length - 1];
			final int kernelHeight = kernelShape[kernelShape.length - 2];
			final int hh = (kernelHeight - 1) / 2;
			final int hw = (kernelWidth - 1) / 2;
			final int inputSize = inputWidth * inputHeight;
			final int inputCount = inputs.getLength() / inputSize; 
			
			for (int i = 0, j = 0; i < inputCount; ++i) {
				for (int y = topOffset; y < inputHeight - bottomOffset; y += strideY) {
					final int top = max(0, y - hh);
					final int bottomEnd = min(top + kernelHeight, inputHeight);
					final int dky = top - (y - hh);
					
					for (int x = leftOffset; x < inputWidth - rightOffset; x += strideX, ++j) {
						final int left = max(0, x - hw);
						final int rightEnd = min(left + kernelWidth, inputWidth);
						final int dkx = left - (x - hw);
						float value = 0F;
						
						for (int yy = top; yy < bottomEnd; ++yy) {
							for (int xx = left; xx < rightEnd; ++xx) {
								final float inputValue = inputs.get(xx + inputWidth * yy + inputSize * i);
								final float kernelValue = kernel.get((dkx + xx - left) + kernelWidth * (dky + yy - top));
								
								value += inputValue * kernelValue;
							}
						}
						
						node.set(j, value);
					}
				}
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final MaxPooling2D node) {
			final Node<?> inputs = node.getInputs();
			final int[] inputsShape = inputs.getShape();
			final int inputHeight = inputsShape[inputsShape.length - 2];
			final int inputWidth = inputsShape[inputsShape.length - 1];
			final int[] offsets = node.getOffsets();
			final int leftOffset = offsets[Node2D.LEFT];
			final int rightOffset = offsets[Node2D.RIGHT];
			final int topOffset = offsets[Node2D.TOP];
			final int bottomOffset = offsets[Node2D.BOTTOM];
			final int[] strides = node.getStrides();
			final int strideX = strides[Node2D.HORIZONTAL];
			final int strideY = strides[Node2D.VERTICAL];
			final int[] kernelShape = node.getKernelShape();
			final int kernelWidth = kernelShape[MaxPooling2D.WIDTH];
			final int kernelHeight = kernelShape[MaxPooling2D.HEIGHT];
			final int hh = (kernelHeight - 1) / 2;
			final int hw = (kernelWidth - 1) / 2;
			final int inputSize = inputWidth * inputHeight;
			final int inputCount = inputs.getLength() / inputSize; 
			
			for (int i = 0, j = 0; i < inputCount; ++i) {
				for (int y = topOffset; y < inputHeight - bottomOffset; y += strideY) {
					final int top = max(0, y - hh);
					final int bottomEnd = min(top + kernelHeight, inputHeight);
					
					for (int x = leftOffset; x < inputWidth - rightOffset; x += strideX, ++j) {
						final int left = max(0, x - hw);
						final int rightEnd = min(left + kernelWidth, inputWidth);
						float value = Float.NEGATIVE_INFINITY;
						
						for (int yy = top; yy < bottomEnd; ++yy) {
							for (int xx = left; xx < rightEnd; ++xx) {
								final float inputValue = inputs.get(xx + inputWidth * yy + inputSize * i);
								
								if (value < inputValue) {
									value = inputValue;
								}
							}
						}
						
						node.set(j, value);
					}
				}
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final Mapping node) {
			final Node<?> argument = node.getArgument();
			final int n = node.getLength();
			final String functionName = node.getFunctionName();
			
			debugPrint(functionName);
			
			switch (functionName) {
			default:
				final List<Object> forward = Mapping.getForward(functionName);
				debugPrint(forward);
				final FloatSupplier output = this.context.newSupplier(forward);
				
				for (int i = 0; i < n; ++i) {
					this.context.getInputs().get(0).set(argument.get(i));
					node.set(i, output.get());
				}
			}
			
			return null;
		}
		
		private static final long serialVersionUID = -8842155630294708599L;
		
		public static final Forwarder INSTANCE = new Forwarder();
		
		/**
		 * @author codistmonk (creation 2016-07-13)
		 */
		public static final class Context implements Serializable {
			
			private final Disjunction<Object, FloatSupplier> rules = new Disjunction<>();
			
			private final List<Variable> inputs = new ArrayList<>();
			
			private final Map<String, Variable> variables = new HashMap<>();
			
			{
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					final autodiff.rules.Variable z = new autodiff.rules.Variable();
					
					this.rules.add(rule($(FORALL, $(x), IN, R, $(y, "=", z)), (__, m) -> {
						final String variableName = (String) m.get(x);
						final Variable variable = new Variable();
						
						if (this.variables.put(variableName, variable) != null) {
							throw new IllegalStateException();
						}
						
						if (this.inputs.isEmpty()) {
							this.inputs.add(variable);
						}
						
						return this.rules.applyTo(m.get(z), m);
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					
					this.rules.add(rule($(ABS, x), (__, m) -> {
						return new Abs(this.rules.applyTo(m.get(x), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					
					this.rules.add(rule($(SQRT, x), (__, m) -> {
						return new Sqrt(this.rules.applyTo(m.get(x), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					
					this.rules.add(rule($(EXP, x), (__, m) -> {
						return new Exp(this.rules.applyTo(m.get(x), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					
					this.rules.add(rule($("-", x), (__, m) -> {
						return new Neg(this.rules.applyTo(m.get(x), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					
					this.rules.add(rule($(LN, x), (__, m) -> {
						return new Ln(this.rules.applyTo(m.get(x), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					
					this.rules.add(rule($(x, "+", y), (__, m) -> {
						return new Plus(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					
					this.rules.add(rule($(x, "-", y), (__, m) -> {
						return new Minus(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					
					this.rules.add(rule($(x, TIMES, y), (__, m) -> {
						return new Times(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
					}));
				}
				
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					
					this.rules.add(rule($(x, "/", y), (__, m) -> {
						return new Div(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
					}));
				}
				
				this.rules.add((object, __) -> object instanceof String, (name, __) -> this.variables.get(name));
				this.rules.add((object, __) -> object instanceof Number, (x, __2) -> new Constant(((Number) x).floatValue()));
			}
			
			public final Disjunction<Object, FloatSupplier> getRules() {
				return this.rules;
			}
			
			public final List<Variable> getInputs() {
				return this.inputs;
			}
			
			public final Map<String, Variable> getVariables() {
				return this.variables;
			}
			
			public final Context reset() {
				this.getInputs().clear();
				this.getVariables().clear();
				
				return this;
			}
			
			public final FloatSupplier newSupplier(final Object definition) {
				return this.reset().getRules().applyTo(definition);
			}
			
			private static final long serialVersionUID = 5823521748135325332L;
			
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-11)
	 */
	public static final class BackwardDiffer implements NodeVisitor<Void> {
		
		private static final long serialVersionUID = -2003909030537706641L;
		
		public static final BackwardDiffer INSTANCE = new BackwardDiffer();
		
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
		
		private static final long serialVersionUID = -654537403002828566L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static abstract class Unary implements FloatSupplier {
		
		private final FloatSupplier source;
		
		protected Unary(final FloatSupplier source) {
			this.source = source;
		}
		
		protected final FloatSupplier getSource() {
			return this.source;
		}
		
		public abstract float diff(float x);
		
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
		
		public abstract float diffLeft(float x, float y);
		
		public abstract float diffRight(float x, float y);
		
		private static final long serialVersionUID = 1573188791368623911L;
		
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
			return forward(this.getSource().get());
		}
		
		@Override
		public final float diff(final float x) {
			return signum(x);
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
			return forward(this.getSource().get());
		}
		
		@Override
		public final float diff(final float x) {
			return (float) (1.0 / (2.0 * sqrt(x)));
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
			return forward(this.getSource().get());
		}
		
		@Override
		public final float diff(final float x) {
			return -1F;
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
			return forward(this.getSource().get());
		}
		
		@Override
		public final float diff(final float x) {
			return this.get();
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
			return forward(this.getSource().get());
		}
		
		@Override
		public final float diff(final float x) {
			return 1F / x;
		}
		
		public static final float forward(final float x) {
			return (float) log(x);
		}
		
		private static final long serialVersionUID = -6123018025469779034L;
		
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
		
		@Override
		public final float diffLeft(final float x, final float y) {
			return 1F;
		}
		
		@Override
		public final float diffRight(final float x, final float y) {
			return 1F;
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
		
		@Override
		public final float diffLeft(final float x, final float y) {
			return 1F;
		}
		
		@Override
		public final float diffRight(final float x, final float y) {
			return -1F;
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
			return this.getLeft().get() * this.getRight().get();
		}
		
		@Override
		public final float diffLeft(final float x, final float y) {
			return y;
		}
		
		@Override
		public final float diffRight(final float x, final float y) {
			return x;
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
			return this.getLeft().get() / this.getRight().get();
		}
		
		@Override
		public final float diffLeft(final float x, final float y) {
			return 1F / y;
		}
		
		@Override
		public final float diffRight(final float x, final float y) {
			return -x / (y * y);
		}
		
		public static final float forward(final float x, final float y) {
			return x / y;
		}
		
		private static final long serialVersionUID = -8379848103818534300L;
		
	}
	
}
