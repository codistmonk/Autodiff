package autodiff.computing;

import static autodiff.computing.Functions.*;
import static autodiff.rules.PatternPredicate.rule;
import static java.lang.Math.*;
import static java.util.Collections.reverse;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.swap;

import autodiff.nodes.Convolution2D;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node;
import autodiff.nodes.Node2D;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Zipping;
import autodiff.rules.Disjunction;
import autodiff.rules.PatternPredicate;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import multij.tools.Pair;
import multij.tools.Tools;

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
	public final <N extends Node<?>> N fullForward(final N node) {
		final List<Node<?>> nodes = new ArrayList<>(node.collectTo(new LinkedHashSet<>()));
		
		reverse(nodes);
		
		nodes.stream().filter(Node::isComputationNode).forEach(n -> this.fill(n, 0F));
		nodes.forEach(n -> n.accept(this.getForwarder()));
		
		return node;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		if (node.setupDiffs()) {
			final Collection<Node<?>> nodes = node.collectTo(new LinkedHashSet<>()).stream().filter(Node::hasDiffs).collect(toList());
			
			nodes.forEach(n -> this.fill(n.getDiffs(), 0F));
			
			this.fill(node.getDiffs(), 1F);
			
			nodes.forEach(n -> n.accept(this.getBackwardDiffer()));
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
		public final Void visit(final MatrixMultiplication node) {
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
						final int rightIndex = transposeRight ? k + c * rightShape[0] : c + k * columns;
						value += left.get(leftIndex) * right.get(rightIndex);
					}
					
					node.set(c + r * columns, value);
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
						
						node.add(j, value);
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
			final List<Object> forwardDefinition = Functions.getDefinition(functionName, 1);
			final FloatSupplier forward = this.context.newSupplier(forwardDefinition);
			
			for (int i = 0; i < n; ++i) {
				this.context.getInputs().get(0).set(argument.get(i));
				
				try {
					node.set(i, forward.get());
				} catch (final Exception e) {
					Tools.debugError(argument.get(i), node.getFunctionName());
					Tools.debugError(argument);
					throw e;
				}
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final Zipping node) {
			final Node<?> left = node.getLeft();
			final Node<?> right = node.getRight();
			final int m = left.getLength();
			final int n = right.getLength();
			final String functionName = node.getFunctionName();
			final List<Object> forwardDefinition = Functions.getDefinition(functionName, 2);
			final FloatSupplier forward = this.context.newSupplier(forwardDefinition);
			
			for (int i = 0; i < m; ++i) {
				this.context.getInputs().get(0).set(left.get(i));
				this.context.getInputs().get(1).set(right.get(i % n));
				
				node.set(i, forward.get());
			}
			
			return null;
		}
		
		private static final long serialVersionUID = -8842155630294708599L;
		
		public static final Forwarder INSTANCE = new Forwarder();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-11)
	 */
	public static final class BackwardDiffer implements NodeVisitor<Void> {
		
		private final Context context = new Context();
				
		@Override
		public final Void visit(final MatrixMultiplication node) {
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
			final Node<?> leftDiffs = left.getDiffs();
			final Node<?> rightDiffs = right.getDiffs();
			
			for (int r = 0; r < rows; ++r) {
				for (int c = 0; c < columns; ++c) {
					final int resultIndex = c + r * columns;
					final float diff = node.getDiffs().get(resultIndex);
					
					for (int k = 0; k < stride; ++k) {
						final int leftIndex = transposeLeft ? r + k * rows : k + r * stride;
						final int rightIndex = transposeRight ? k + c * rightShape[0] : c + k * columns;
						
						if (leftDiffs != null) {
							leftDiffs.add(leftIndex, right.get(rightIndex) * diff);
						}
						
						if (rightDiffs != null) {
							rightDiffs.add(rightIndex, left.get(leftIndex) * diff);
						}
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
						int valueIndex = -1;
						
						for (int yy = top; yy < bottomEnd; ++yy) {
							for (int xx = left; xx < rightEnd; ++xx) {
								final int inputIndex = xx + inputWidth * yy + inputSize * i;
								final float inputValue = inputs.get(inputIndex);
								
								if (value < inputValue) {
									value = inputValue;
									valueIndex = inputIndex;
								}
							}
						}
						
						node.getArgument().getDiffs().add(valueIndex, node.getDiffs().get(j));
					}
				}
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
			final Node<?> inputsDiffs = inputs.getDiffs();
			final Node<?> kernelDiffs = kernel.getDiffs();
			
			for (int i = 0, j = 0; i < inputCount; ++i) {
				for (int y = topOffset; y < inputHeight - bottomOffset; y += strideY) {
					final int top = max(0, y - hh);
					final int bottomEnd = min(top + kernelHeight, inputHeight);
					final int dky = top - (y - hh);
					
					for (int x = leftOffset; x < inputWidth - rightOffset; x += strideX, ++j) {
						final int left = max(0, x - hw);
						final int rightEnd = min(left + kernelWidth, inputWidth);
						final int dkx = left - (x - hw);
						final float diff = node.getDiffs().get(j);
						
						for (int yy = top; yy < bottomEnd; ++yy) {
							for (int xx = left; xx < rightEnd; ++xx) {
								final int inputIndex = xx + inputWidth * yy + inputSize * i;
								final int kernelIndex = (dkx + xx - left) + kernelWidth * (dky + yy - top);
								
								if (inputsDiffs != null) {
									final float kernelValue = kernel.get(kernelIndex);
									
									inputs.getDiffs().add(inputIndex, kernelValue * diff);
								}
								
								if (kernelDiffs != null) {
									final float inputValue = inputs.get(inputIndex);
									
									kernel.getDiffs().add(kernelIndex, inputValue * diff);
								}
							}
						}
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
			final List<Object> argumentDiffDefinition = Functions.getDiffDefinition(functionName, 1);
			final FloatSupplier argumentDiff = this.context.newSupplier(argumentDiffDefinition);
			
			for (int i = 0; i < n; ++i) {
				this.context.getInputs().get(0).set(argument.get(i));
				node.getArgument().getDiffs().add(i, argumentDiff.get() * node.getDiffs().get(i));
			}
			
			return null;
		}
		
		@Override
		public final Void visit(final Zipping node) {
			final Node<?> left = node.getLeft();
			final Node<?> right = node.getRight();
			final int m = left.getLength();
			final int n = right.getLength();
			final String functionName = node.getFunctionName();
			final Node<?> leftDiffs = left.getDiffs();
			final Node<?> rightDiffs = right.getDiffs();
			
			if (leftDiffs != null) {
				final List<Object> leftDiffDefinition = Functions.getDiffDefinition(functionName, 2, 0);
				final FloatSupplier leftDiff = this.context.newSupplier(leftDiffDefinition);
				
				for (int i = 0; i < m; ++i) {
					final float diff = node.getDiffs().get(i);
					
					this.context.getInputs().get(0).set(left.get(i));
					this.context.getInputs().get(1).set(right.get(i % n));
					
					leftDiffs.add(i, leftDiff.get() * diff);
				}
			}
			
			if (rightDiffs != null) {
				final List<Object> rightDiffDefinition = Functions.getDiffDefinition(functionName, 2, 1);
				final FloatSupplier rightDiff = this.context.newSupplier(rightDiffDefinition);
				
				for (int i = 0; i < m; ++i) {
					final float diff = node.getDiffs().get(i);
					
					this.context.getInputs().get(0).set(left.get(i));
					this.context.getInputs().get(1).set(right.get(i % n));
					
					rightDiffs.add(i % n, rightDiff.get() * diff);
				}
			}
			
			return null;
		}
		
		private static final long serialVersionUID = -2003909030537706641L;
		
		public static final BackwardDiffer INSTANCE = new BackwardDiffer();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-13)
	 */
	public static final class Context implements Serializable {
		
		private final Disjunction<Object, FloatSupplier> rules = new Disjunction<>();
		
		private final List<Variable> inputs = new ArrayList<>();
		
		private final Map<Object, Variable> variables = new HashMap<>();
		
		{
			for (final List<Object> definition : Functions.getDefinitions().values()) {
				{
					final autodiff.rules.Variable x = new autodiff.rules.Variable();
					final autodiff.rules.Variable y = new autodiff.rules.Variable();
					final autodiff.rules.Variable z = new autodiff.rules.Variable();
					final List<Object> function1DefinitionPattern = $(FORALL, $(x), IN, R, $(y, "=", z));
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
					final List<Object> function2DefinitionPattern = $(FORALL, $(x0, x1), IN, R, $(y, "=", z));
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
				
				this.rules.add(rule($(SIN, x), (__, m) -> {
					return new Sin(this.rules.applyTo(m.get(x), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				
				this.rules.add(rule($(COS, x), (__, m) -> {
					return new Cos(this.rules.applyTo(m.get(x), m));
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
				
				this.rules.add(rule($(x, "*", y), (__, m) -> {
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
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, "=", y), (__, m) -> {
					return new Equal(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, "!=", y), (__, m) -> {
					return new NotEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, "<", y), (__, m) -> {
					return new Less(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, "<=", y), (__, m) -> {
					return new LessOrEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, ">", y), (__, m) -> {
					return new Greater(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			{
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				
				this.rules.add(rule($(x, ">=", y), (__, m) -> {
					return new GreaterOrEqual(this.rules.applyTo(m.get(x), m), this.rules.applyTo(m.get(y), m));
				}));
			}
			
			this.rules.add((object, __) -> object instanceof autodiff.rules.Variable, (name, m) -> {
				final Object value = transitiveGet(m, name);
				
				if (value instanceof FloatSupplier) {
					return (FloatSupplier) value;
				}
				
				return this.rules.applyTo(value, m);
			});
			this.rules.add((object, __) -> object instanceof Number, (x, __) -> new Constant(((Number) x).floatValue()));
		}
		
		public final Disjunction<Object, FloatSupplier> getRules() {
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
				final autodiff.rules.Variable x = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				final autodiff.rules.Variable z = new autodiff.rules.Variable();
				final List<Object> function1DefinitionPattern = $(FORALL, $(x), IN, R, $(y, "=", z));
				final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
				
				if (autodiff.rules.Variable.match(function1DefinitionPattern, definition, mapping)) {
					final Variable variable = new Variable();
					
					if (this.variables.put(x, variable) != null) {
						throw new IllegalStateException();
					}
					
					if (this.inputs.isEmpty()) {
						this.inputs.add(variable);
					}
					
					final Map<Object, Object> m_ = new HashMap<>();
					m_.put(mapping.get(x), x);
					final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
					
					mapping.put(x, variable);
					
					return this.rules.applyTo(z_, mapping);
				}
			}
			
			{
				final autodiff.rules.Variable x0 = new autodiff.rules.Variable();
				final autodiff.rules.Variable x1 = new autodiff.rules.Variable();
				final autodiff.rules.Variable y = new autodiff.rules.Variable();
				final autodiff.rules.Variable z = new autodiff.rules.Variable();
				final List<Object> function2DefinitionPattern = $(FORALL, $(x0, x1), IN, R, $(y, "=", z));
				final Map<autodiff.rules.Variable, Object> mapping = new HashMap<>();
				
				if (autodiff.rules.Variable.match(function2DefinitionPattern, definition, mapping)) {
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
					final Object z_ = autodiff.rules.Variable.rewrite(mapping.get(z), m_);
					
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
