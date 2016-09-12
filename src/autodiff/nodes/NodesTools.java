package autodiff.nodes;

import static autodiff.computing.Functions.INFIX_OPERATORS;
import static autodiff.computing.Functions.KRONECKER;
import static autodiff.computing.Functions.POSTFIX_OPERATORS;
import static autodiff.computing.Functions.PREFIX_OPERATORS;
import static autodiff.computing.Functions.ROUND;
import static autodiff.computing.Functions.STEP1;
import static multij.tools.Tools.*;

import autodiff.computing.DefaultProcessor;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.Supplier;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-15)
 */
public final class NodesTools {

	private NodesTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final String SUM = "sum";
	
	public static final String T = "^T";
	
	/**
	 * Not an Index.
	 */
	public static final float NaI = -Integer.MAX_VALUE;
	
	private static final AtomicLong lastId = new AtomicLong(-1L);
	
	public static final long newId() {
		return lastId.incrementAndGet();
	}
	
	public static final Node<?> sortIndices(final Node<?> inputs) {
		return new SortIndices().setInputs(inputs).autoShape();
	}
	
	public static final Node<?> indexGreaterness(final int n) {
		return new IndexGreaterness(n).autoShape();
	}
	
	public static final Node<?> percentileMask(final Node<?> inputs, final Node<?> ratio) {
		return new PercentileMask().setInputs(inputs).setRatio(ratio).autoShape();
	}
	
	public static final Node<?> percentile(final Node<?> inputs, final Node<?> ratio) {
		return new Percentile().setInputs(inputs).setRatio(ratio).autoShape();
	}
	
	public static final Node<?> maxPooling(final Node<?> inputs, final int[] offsets, final int[] strides, final int[] kernelShape) {
		final GridSampling grid = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		final PatchSampling patch = new PatchSampling(grid).setPatchShape(kernelShape);
		
		return maxPooling(inputs, patch);
	}
	
	public static final Node<?> maxPooling(final Node<?> inputs, final PatchSampling sampling) {
		return new MaxPooling(sampling).setInputs(inputs).autoShape();
	}
	
	public static final Node<?> convolutions(final Node<?> inputs, final int[] offsets, final int[] strides, final Node<?> kernel) {
		final GridSampling sampling = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		
		return convolutions(inputs, sampling, kernel);
	}
	
	public static final Node<?> convolutions(final Node<?> inputs, final GridSampling sampling, final Node<?> kernel) {
		return new Convolutions(sampling).setInputs(inputs).setKernels(kernel).autoShape();
	}
	
	public static final Node<?> patches(final Node<?> inputs, final int[] offsets, final int[] strides, final int[] patchShape) {
		final GridSampling grid = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		
		return patches(inputs, new PatchSampling(grid).setPatchShape(patchShape));
	}
	
	public static final Node<?> patches(final Node<?> inputs, final PatchSampling sampling) {
		return new Patches(sampling).setInputs(inputs).autoShape();
	}
	
	public static final Node<?> selection(final Node<?> vectors, final Node<?> indices) {
		return new Selection().setVectors(vectors).setIndices(indices).autoShape();
	}
	
	public static final Node<?> repeatAndIncrease(final int delta, final int n, final int stride) {
		if (true) {
			return Computation.repeatAndIncrease()
					.set("n", n)
					.set("stride", stride)
					.set("delta", delta)
					.autoShape();
		}
		
		return new RepeatAndIncrease(delta, n, stride).autoShape();
	}
	
	public static final Node<?> innerReplicator(final int stride, final int replications) {
		if (true) {
			return Computation.innerReplicator()
					.set("stride", stride)
					.set("n", replications)
					.autoShape();
		}
		
		return new InnerReplicator(stride, replications).autoShape();
	}
	
	public static final Node<?> outerReplicator(final int stride, final int replications) {
		if (true) {
			return Computation.outerReplicator()
					.set("stride", stride)
					.set("n", replications)
					.autoShape();
		}
		
		return new OuterReplicator(stride, replications).autoShape();
	}
	
	public static final Node<?> range(final int n) {
		if (true) {
			return Computation.range().set("n", n).autoShape();
		}
		
		return new Range(n).autoShape();
	}
	
	public static final Node<?> sum(final Node<?> argument, final int... strides) {
		return new Sum(strides).setArgument(argument).autoShape();
	}
	
	public static final Node<?> merge(final int dimensionIndex, final Node<?>... arguments) {
		return new Merge(dimensionIndex).setArguments(arguments).autoShape();
	}
	
	public static final int[] indexToCartesian(final int[] lengths, final int index, final int[] result) {
		final int n = lengths.length;
		
		for (int i = n - 1, tmp = index; 0 <= i; --i) {
			result[i] = tmp % lengths[i];
			tmp /= lengths[i];
		}
		
		return result;
	}
	
	public static final int indexFromCartesian(final int[] lengths, final int[] indices) {
		int result = indices[0];
		
		for (int i = 1; i < indices.length; ++i) {
			result = indices[i] + lengths[i] * result;
		}
		
		return result;
	}
	
	public static final int[] bounds(final int... lengths) {
		final int n = lengths.length;
		final int[] result = new int[n * 2];
		
		for (int i = 0; i < n; ++i) {
			result[2 * i + 1] = lengths[i] - 1;
		}
		
		return result;
	}
	
	public static final Node<?> shape(final Node<?> node, final int... shape) {
		return Arrays.equals(node.getShape(), shape) ? node : new Data().setStorage(node).setShape(shape);
	}
	
	public static final Node<?> ones(final int... shape) {
		if (true) {
			return Computation.ones().set("shape", shape).autoShape();
		}
		
		return new Ones(shape).autoShape();
	}
	
	public static final void checkLength(final int expectedLength, final int actualLength) {
		check(expectedLength == actualLength, () -> "Expected length: " + expectedLength + ", actual: " + actualLength);
	}
	
	public static final void check(final boolean b, final Supplier<String> errorMessage) {
		if (!b) {
			throw new RuntimeException(errorMessage.get());
		}
	}
	
	public static final int product(final int... values) {
		return subproduct(values, 0);
	}
	
	public static final int subproduct(final int[] values, final int begin) {
		return subproduct(values, begin, values.length);
	}
	
	public static final int subproduct(final int[] values, final int begin, final int end) {
		int result = 1;
		
		for (int i = begin; i < end; ++i) {
			result *= values[i];
		}
		
		return result;
	}
	
	public static final Node<?> $(final Object... objects) {
		final int n = objects.length;
		
		if (n == 1) {
			final Node<?> node = cast(Node.class, objects[0]);
			
			if (node != null) {
				return node;
			}
		}
		
		try {
			final Node<?> data = new Data().setShape(n);
			
			for (int i = 0; i < n; ++i) {
				data.set(i, ((Number) objects[i]).floatValue());
			}
			
			return data;
		} catch (final Exception exception) {
			ignore(exception);
		}
		
		if (n == 4) {
			if (T.equals(objects[1]) && T.equals(objects[3])) {
				return new MatrixMultiplication().setLeft($(objects[0])).setTransposeLeft(true).setRight($(objects[2])).setTransposeRight(true).autoShape();
			}
		}
		
		if (n == 3) {
			if (T.equals(objects[1])) {
				return new MatrixMultiplication().setLeft($(objects[0])).setTransposeLeft(true).setRight($(objects[2])).autoShape();
			}
			
			if (T.equals(objects[2])) {
				return new MatrixMultiplication().setLeft($(objects[0])).setRight($(objects[1])).setTransposeRight(true).autoShape();
			}
			
			if (INFIX_OPERATORS.contains(objects[1])) {
				return new Zipping().setLeft($(objects[0])).setRight($(objects[2])).setFunctionName(objects[1].toString()).autoShape();
			}
			
			if (PREFIX_OPERATORS.contains(objects[0])) {
				return new Zipping().setLeft($(objects[1])).setRight($(objects[2])).setFunctionName(objects[0].toString()).autoShape();
			}
			
			if (SUM.equals(objects[0])) {
				return sum($(objects[2]), (int[]) objects[1]);
			}
			
			if ("@".equals(objects[1])) {
				return selection($(objects[0]), $(objects[2]));
			}
		}
		
		if (n == 2) {
			if (PREFIX_OPERATORS.contains(objects[0])) {
				return new Mapping().setArgument($(objects[1])).setFunctionName(objects[0].toString()).autoShape();
			}
			
			if (POSTFIX_OPERATORS.contains(objects[1])) {
				return new Mapping().setArgument($(objects[0])).setFunctionName(objects[1].toString()).autoShape();
			}
			
			if (SUM.equals(objects[0])) {
				return sum($(objects[1]));
			}
			
			final Node<?> left = cast(Node.class, $(objects[0]));
			final Node<?> right = cast(Node.class, $(objects[1]));
			
			if (left != null && right != null) {
				return new MatrixMultiplication().setLeft(left).setRight(right).autoShape();
			}
		}
		
		throw new IllegalArgumentException(Arrays.toString(objects));
	}
	
	/**
	 * @author codistmonk (creation 2016-07-29)
	 */
	public static final class GridSampling implements Serializable {
		
		private int[] inputsShape;
		
		private int[] offsets = { 0, 0, 0, 0 };
		
		private int[] strides = { 1, 1 };
		
		public final int getInputCount() {
			return product(this.getInputsShape()) / this.getInputSize();
		}
		
		public final int getInputSize() {
			return this.getInputWidth() * this.getInputHeight() * this.getInputChannels();
		}
		
		public final int getOutputSize() {
			return this.getOutputWidth() * this.getOutputHeight();
		}

		public final int getOutputHeight() {
			return (this.getInputHeight() - this.getOffsets()[TOP_OFFSET] - this.getOffsets()[BOTTOM_OFFSET] + this.getStrides()[VERTICAL_STRIDE] - 1) / this.getStrides()[VERTICAL_STRIDE];
		}
		
		public final int getOutputWidth() {
			return (this.getInputWidth() - this.getOffsets()[LEFT_OFFSET] - this.getOffsets()[RIGHT_OFFSET] + this.getStrides()[HORIZONTAL_STRIDE] - 1) / this.getStrides()[HORIZONTAL_STRIDE];
		}
		
		public final int getInputChannels() {
			return this.getInputsShape()[this.getInputsShape().length - 3];
		}
		
		public final int getInputHeight() {
			return this.getInputsShape()[this.getInputsShape().length - 2];
		}
		
		public final int getInputWidth() {
			return this.getInputsShape()[this.getInputsShape().length - 1];
		}
		
		public final int[] getInputsShape() {
			return this.inputsShape;
		}
		
		public final GridSampling setInputsShape(final int... inputsShape) {
			this.inputsShape = inputsShape;
			
			return this;
		}
		
		public final int[] getOffsets() {
			return this.offsets;
		}
		
		public final GridSampling setOffsets(final int... offsets) {
			this.offsets = offsets;
			
			return this;
		}
		
		public final int[] getStrides() {
			return this.strides;
		}
		
		public final GridSampling setStrides(final int... strides) {
			this.strides = strides;
			
			return this;
		}
		
		public final void forEach(final Consumer<int[]> f) {
			final int inputHeight = this.getInputHeight();
			final int inputWidth = this.getInputWidth();
			final int inputChannels = this.getInputChannels();
			final int topOffset = this.getOffsets()[TOP_OFFSET];
			final int bottomOffset = this.getOffsets()[BOTTOM_OFFSET];
			final int verticalStride = this.getStrides()[VERTICAL_STRIDE];
			final int leftOffset = this.getOffsets()[LEFT_OFFSET];
			final int rightOffset = this.getOffsets()[RIGHT_OFFSET];
			final int horizontalStride = this.getStrides()[HORIZONTAL_STRIDE];
			final int[] var = new int[3];
			
			for (var[Y] = topOffset; var[Y] < inputHeight - bottomOffset; var[Y] += verticalStride) {
				for (var[X] = leftOffset; var[X] < inputWidth - rightOffset; var[X] += horizontalStride) {
					for (var[C] = 0; var[C] < inputChannels; ++var[C]) {
						f.accept(var);
					}
				}
			}
		}
		
		private static final long serialVersionUID = 5296906932828451007L;
		
		public static final int LEFT_OFFSET = 0;
		
		public static final int RIGHT_OFFSET = 1;
		
		public static final int TOP_OFFSET = 2;
		
		public static final int BOTTOM_OFFSET = 3;
		
		public static final int HORIZONTAL_STRIDE = 0;
		
		public static final int VERTICAL_STRIDE = 1;
		
		public static final int C = 0;
		
		public static final int Y = 1;
		
		public static final int X = 2;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-29)
	 */
	public static final class PatchSampling implements Serializable {
		
		private final GridSampling sampling;
		
		private int[] patchShape;
		
		public PatchSampling(final GridSampling sampling) {
			this.sampling = sampling;
		}
		
		public final int getPatchSize() {
			return this.getPatchWidth() * this.getPatchHeight() * getPatchChannels();
		}
		
		public final int getPatchChannels() {
			return this.getSampling().getInputChannels();
		}
		
		public final int getPatchHeight() {
			return this.getPatchShape()[this.getPatchShape().length - 2];
		}
		
		public final int getPatchWidth() {
			return this.getPatchShape()[this.getPatchShape().length - 1];
		}
		
		public final GridSampling getSampling() {
			return this.sampling;
		}
		
		public final int[] getPatchShape() {
			return this.patchShape;
		}
		
		public final PatchSampling setPatchShape(final int... patchShape) {
			this.patchShape = patchShape;
			
			return this;
		}
		
		public final void forEachPixelAround(final int[] centerPixel, final Consumer<int[]> f) {
			final int patchHeight = this.getPatchHeight();
			final int patchWidth = this.getPatchWidth();
			final int y = centerPixel[GridSampling.Y];
			final int x = centerPixel[GridSampling.X];
			final int[] var = new int[3];
			
			var[GridSampling.C] = centerPixel[GridSampling.C];
			
			for (int i = 0; i < patchHeight; ++i) {
				var[GridSampling.Y] = y - (patchHeight - 1) / 2 + i;
				
				for (int j = 0; j < patchWidth; ++j) {
					var[GridSampling.X] = x - (patchWidth - 1) / 2 + j;
					
					f.accept(var);
				}
			}
		}
		
		private static final long serialVersionUID = 7162845996889119853L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-02)
	 */
	public static final class Range extends CustomNode<Range> {
		
		private final int n;
		
		public Range(final int n) {
			this.n = n;
		}
		
		@Override
		public final Range autoShape() {
			return this.setShape(this.n);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			
			for (int i = 0; i < this.n; ++i) {
				result.set(i, i);
			}
			
			return result;
		}
		
		private static final long serialVersionUID = 3288108223610832677L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-03)
	 */
	public static final class Sum extends CustomNode<Sum> {
		
		private final int[] strides;
		
		public Sum(final int... strides) {
			super(Arrays.asList((Node<?>) null));
			this.strides = strides;
		}
		
		public final Node<?> getArgument() {
			return this.getArguments().get(0);
		}
		
		public final Sum setArgument(final Node<?> argument) {
			this.getArguments().set(0, argument);
			
			return this;
		}
		
		@Override
		public final Sum autoShape() {
			if (this.strides.length == 0) {
				return this.setShape(1);
			}
			
			final Node<?> argument = this.getArgument();
			final int[] resultShape = argument.getLengths(new int[this.strides.length]);
			
			for (int i = 0; i < this.strides.length; ++i) {
				if (resultShape[i] % this.strides[i] != 0) {
					throw new IllegalArgumentException(resultShape[i] + " not divisible by " + this.strides[i]);
				}
				
				resultShape[i] /= this.strides[i];
			}
			
			return this.setShape(resultShape);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> argument = this.getArgument();
			
			if (this.strides.length == 0) {
				final int n = argument.getLength();
				final Node<?> mul = $(shape(argument, 1, n), ones(n, 1));
				
				mul.setStorage(this);
				
				return shape(mul, 1);
			}
			
			final int[] resultShape = this.getShape();
			final int m = argument.getLength();
			final int n = product(resultShape);
			final Node<?> right = new Data().setShape(m, n);
			final int[] argumentShape = argument.getLengths(new int[this.strides.length]);
			final int[] outerBounds = bounds(resultShape);
			final int[] innerBounds = bounds(this.strides);
			
			for (final int[] i : cartesian(outerBounds)) {
				for (int j = 0; j < i.length; ++j) {
					innerBounds[2 * j + 0] = i[j] * this.strides[j];
					innerBounds[2 * j + 1] = i[j] * this.strides[j] + this.strides[j] - 1;
				}
				
				final int outputIndex = indexFromCartesian(resultShape, i);
				
				for (final int[] j : cartesian(innerBounds)) {
					final int k = indexFromCartesian(argumentShape, j);
					
					right.set(outputIndex + n * k, 1F);
				}
			}
			
			final Node<?> mul = $(shape(argument, 1, m), right);
			
			mul.setStorage(this);
			
			return shape(mul, resultShape);
		}
		
		private static final long serialVersionUID = -7076790199639726703L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-07)
	 */
	public static final class Merge extends CustomNode<Merge> {
		
		private final int dimensionIndex;
		
		public Merge(final int dimensionIndex) {
			super(new ArrayList<>());
			this.dimensionIndex = dimensionIndex;
		}
		
		public final Merge setArguments(final Node<?>... arguments) {
			this.getArguments().clear();
			
			for (final Node<?> argument : arguments) {
				this.getArguments().add(argument);
			}
			
			return this;
		}
		
		@Override
		public final Merge autoShape() {
			final int[] shape = this.getArguments().get(0).getShape().clone();
			final int n = this.getArguments().size();
			
			for (int i = 1; i < n; ++i) {
				final int[] argumentShape = this.getArguments().get(i).getShape();
				
				checkLength(shape.length, argumentShape.length);
				
				for (int j = 0; j < shape.length; ++j) {
					check(j == this.dimensionIndex || shape[j] == argumentShape[j], () ->
					"Incompatible dimensions: " + Arrays.toString(shape)
					+ " cannot be merged with " + Arrays.toString(argumentShape) + " at index " + this.dimensionIndex);
				}
				
				shape[this.dimensionIndex] += argumentShape[this.dimensionIndex];
			}
			
			return this.setShape(shape);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final int chunkCount = subproduct(this.getShape(), 0, this.dimensionIndex);
			final int n = this.getLength();
			final int stride = n / chunkCount;
			int offset = 0;
			Node<?> sum = null;
			
			for (final Node<?> argument : this.getArguments()) {
				final Node<?> indices = new Data().setShape(1, n);
				final int chunkSize = subproduct(argument.getShape(), this.dimensionIndex);
				
				DefaultProcessor.INSTANCE.fill(indices, NaI);
				
				for (int i = offset, k = 0; i < n; i += stride) {
					for (int j = 0; j < chunkSize; ++j, ++k) {
						indices.set(i + j, k);
					}
				}
				
				final Node<?> selection = selection(shape(argument, 1, argument.getLength()), indices);
				
				if (sum == null) {
					sum = selection;
				} else {
					sum = $(sum, "+", selection);
				}
				
				offset += chunkSize;
			}
			
			sum.setStorage(this);
			
			return shape(sum, this.getShape());
		}
		
		private static final long serialVersionUID = -2218885137190293263L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-03)
	 */
	public static final class InnerReplicator extends CustomNode<InnerReplicator> {
		
		private final int stride;
		
		private final int replications;
		
		public InnerReplicator(final int stride, final int replications) {
			this.stride = stride;
			this.replications = replications;
		}
		
		@Override
		public final InnerReplicator autoShape() {
			return this.setShape(this.stride, this.stride * this.replications);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			
			for (int i = 0; i < this.stride; ++i) {
				for (int j = 0; j < this.replications; ++j) {
					result.set(j + (this.stride + 1) * this.replications * i, 1);
				}
			}
			
			return result;
		}
		
		private static final long serialVersionUID = 5973922326300037152L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-03)
	 */
	public static final class OuterReplicator extends CustomNode<OuterReplicator> {
		
		private final int stride;
		
		private final int replications;
		
		public OuterReplicator(final int stride, final int replications) {
			this.stride = stride;
			this.replications = replications;
		}
		
		@Override
		public final OuterReplicator autoShape() {
			return this.setShape(this.stride, this.stride * this.replications);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			
			for (int i = 0; i < this.stride; ++i) {
				for (int j = 0; j < this.replications; ++j) {
					result.set(i + this.stride * j + this.stride * this.replications * i, 1);
				}
			}
			
			return result;
		}
		
		private static final long serialVersionUID = -3214753210439048412L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-03)
	 */
	public static final class RepeatAndIncrease extends CustomNode<RepeatAndIncrease> {
		
		private final int vectorCount;
		
		private final int indicesCount;
		
		private final int indicesStride;
		
		public RepeatAndIncrease(final int vectorCount, final int indicesCount, final int indicesStride) {
			this.vectorCount = vectorCount;
			this.indicesCount = indicesCount;
			this.indicesStride = indicesStride;
		}
		
		@Override
		public final RepeatAndIncrease autoShape() {
			return this.setShape(this.indicesCount * this.indicesStride);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			
			for (int i = 1; i < this.indicesCount; ++i) {
				for (int j = 0; j < this.indicesStride; ++j) {
					result.set(j + this.indicesStride * i, this.vectorCount * i);
				}
			}
			
			return result;
		}
		
		private static final long serialVersionUID = 5715035072333159555L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class Selection extends CustomNode<Selection> {
		
		public Selection() {
			super(Arrays.asList(new Node[2]));
		}
		
		public final Node<?> getVectors() {
			return this.getArguments().get(0);
		}
		
		public final Selection setVectors(final Node<?> vectors) {
			this.getArguments().set(0, vectors);
			
			return this;
		}
		
		public final Node<?> getIndices() {
			return this.getArguments().get(1);
		}
		
		public final Selection setIndices(final Node<?> indices) {
			this.getArguments().set(1, indices);
			
			return this;
		}
		
		@Override
		public final Selection autoShape() {
			final Node<?> vectors = this.getArguments().get(0);
			final Node<?> indices = this.getArguments().get(1);
			final int[] vectorsShape = vectors.getLengths(new int[2]);
			final int[] indicesShape = indices.getLengths(new int[2]);
			final int vectorCount = vectorsShape[1];
			final int indicesCount = indicesShape[0];
			final int vectorsStride = vectorCount * indicesCount;
			final int m = vectors.getLength() / vectorsStride;
			final int n = indices.getLength();
			
			return this.setShape(m, n);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> vectors = this.getArguments().get(0);
			final Node<?> indices = this.getArguments().get(1);
			final int[] vectorsShape = vectors.getLengths(new int[2]);
			final int[] indicesShape = indices.getLengths(new int[2]);
			final int vectorCount = vectorsShape[1];
			final int indicesCount = indicesShape[0];
			final int indicesStride = indicesShape[1];
			final int vectorsStride = vectorCount * indicesCount;
			final Node<?> shiftData = repeatAndIncrease(vectorCount, indicesCount, indicesStride);
			final Node<?> shift = $(indices, "+", shiftData);
			final Node<?> replicationMatrix = innerReplicator(indicesStride, vectorsStride);
			final Node<?> replicatedIndices = $(shape(shift, indices.getLength() / indicesStride, indicesStride), replicationMatrix);
			final Node<?> range = range(vectorsStride);
			final Node<?> mask = $(KRONECKER, replicatedIndices, range);
			final Node<?> mul = $(shape(vectors, vectors.getLength() / vectorsStride, vectorsStride),
					shape(mask, mask.getLength() / vectorsStride, vectorsStride), T);
			
			mul.setStorage(this);
			
			return shape(mul, this.getShape());
		}
		
		private static final long serialVersionUID = 7244337174139272122L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-03)
	 */
	public static final class SortIndices extends CustomNode<SortIndices> {
		
		public SortIndices() {
			super(Arrays.asList(new Node[1]));
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final SortIndices setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		@Override
		public final SortIndices autoShape() {
			final int[] inputsShape = this.getInputs().getShape();
			
			checkLength(2, inputsShape.length);
			
			return this.setShape(inputsShape);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> inputs = this.getInputs();
			final int[] inputsShape = inputs.getShape();
			final int n = inputsShape[1];
			final Node<?> innerReplicator = innerReplicator(n, n);
			final Node<?> outerReplicator = outerReplicator(n, n);
			final Node<?> inrep = $(inputs, innerReplicator);
			final Node<?> outrep = $(inputs, outerReplicator);
			final Node<?> difference = $(inrep, "-", outrep);
			final Node<?> greaterness = $(STEP1, difference);
			final Node<?> equality = $(KRONECKER, inrep, outrep);
			final Node<?> indexGreaterness = indexGreaterness(n);
			final Node<?> aboveness = $(greaterness, "+", $(equality, "*", indexGreaterness));
			
			return sum(aboveness, 1, n).setStorage(this);
		}
		
		private static final long serialVersionUID = 2694700094496290472L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class IndexGreaterness extends CustomNode<IndexGreaterness> {
		
		private final int n;
		
		public IndexGreaterness(final int n) {
			this.n = n;
		}
		
		@Override
		public final IndexGreaterness autoShape() {
			return this.setShape(1, this.n * this.n);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			
			for (int i = 0; i < this.n; ++i) {
				for (int j = 0; j < i; ++j) {
					result.set(j + this.n * i, 1F);
				}
			}
			
			return result;
		}
		
		private static final long serialVersionUID = 4622261733770952111L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class Patches extends CustomNode<Patches> {
		
		private final PatchSampling sampling;
		
		public Patches(final PatchSampling sampling) {
			super(Arrays.asList(new Node[1]));
			this.sampling = sampling;
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final Patches setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		@Override
		public final Patches autoShape() {
			final GridSampling grid = this.sampling.getSampling();
			final int inputCount = grid.getInputCount();
			final int outputSize = grid.getOutputSize();
			final int inputChannels = grid.getInputChannels();
			final int patchWidth = this.sampling.getPatchWidth();
			final int patchHeight = this.sampling.getPatchHeight();
			
			return this.setShape(inputCount * outputSize, inputChannels, patchHeight, patchWidth);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final GridSampling grid = this.sampling.getSampling();
			final int inputWidth = grid.getInputWidth();
			final int inputHeight = grid.getInputHeight();
			final int outputSize = grid.getOutputSize();
			final int inputSize = grid.getInputSize();
			final int inputCount = grid.getInputCount();
			final int patchSize = this.sampling.getPatchSize();
			final Node<?> indices = new Data().setShape(1, patchSize * outputSize);
			
			{
				final int[] o = { 0 };
				
				grid.forEach(centerPixel -> {
					this.sampling.forEachPixelAround(centerPixel, p -> {
						final int c = centerPixel[GridSampling.C];
						final int yy = p[GridSampling.Y];
						final int xx = p[GridSampling.X];
						
						if (0 <= yy && yy < inputHeight && 0 <= xx && xx < inputWidth) {
							indices.set(o[0], xx + inputWidth * (yy + inputHeight * c));
						} else {
							indices.set(o[0], NaI);
						}
						
						++o[0];
					});
				});
			}
			
			final Node<?> selection = selection(shape(this.getInputs(), inputCount, inputSize), indices);
			
			selection.setStorage(this);
			
			return shape(selection, this.getShape());
		}
		
		private static final long serialVersionUID = -4980999950245486248L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class Convolutions extends CustomNode<Convolutions> {
		
		private final GridSampling sampling;
		
		public Convolutions(final GridSampling sampling) {
			super(Arrays.asList(new Node[2]));
			this.sampling = sampling;
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final Convolutions setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		public final Node<?> getKernels() {
			return this.getArguments().get(1);
		}
		
		public final Convolutions setKernels(final Node<?> kernels) {
			this.getArguments().set(1, kernels);
			
			return this;
		}
		
		@Override
		public final Convolutions autoShape() {
			final int[] inputsShape = this.getInputs().getShape();
			final int[] kernelsShape = this.getKernels().getShape();
			
			checkLength(4, inputsShape.length);
			checkLength(4, kernelsShape.length);
			checkLength(inputsShape[1], kernelsShape[1]);
			
			return this.setShape(this.sampling.getInputCount(), kernelsShape[0], this.sampling.getOutputHeight(), this.sampling.getOutputWidth());
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> inputs = this.getInputs();
			final Node<?> kernels = this.getKernels();
			final Node<?> patches = patches(inputs, new PatchSampling(this.sampling).setPatchShape(kernels.getShape()));
			final int[] kernelsShape = kernels.getLengths(new int[2]);
			final int kernelLength = kernelsShape[kernelsShape.length - 1];
			
			final Node<?> mul = $(
					shape(kernels, kernels.getLength() / kernelLength, kernelLength), 
					shape(patches, patches.getLength() / kernelLength, kernelLength), T);
			
			mul.setStorage(this);
			
			return shape(mul, this.getShape());
		}
		
		private static final long serialVersionUID = -9102153974630246500L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class MaxPooling extends CustomNode<MaxPooling> {
		
		private final PatchSampling sampling;
		
		public MaxPooling(final PatchSampling sampling) {
			super(Arrays.asList(new Node[1]));
			this.sampling = sampling;
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final MaxPooling setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		@Override
		public final MaxPooling autoShape() {
			final GridSampling grid = this.sampling.getSampling();
			
			return this.setShape(grid.getInputCount(), grid.getInputChannels(), grid.getOutputHeight(), grid.getOutputWidth());
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> patches = patches(this.getInputs(), this.sampling);
			final int[] patchesShape = patches.getShape();
			final Node<?> percentile = percentile(shape(
					patches, patchesShape[0] * patchesShape[1], patchesShape[2] * patchesShape[3]), $(1F));
			
			percentile.setStorage(this);
			
			return shape(percentile, this.getShape());
		}
		
		private static final long serialVersionUID = -24236175911223991L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class PercentileMask extends CustomNode<PercentileMask> {
		
		public PercentileMask() {
			super(Arrays.asList(new Node[2]));
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final PercentileMask setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		public final Node<?> getRatio() {
			return this.getArguments().get(1);
		}
		
		public final PercentileMask setRatio(final Node<?> ratio) {
			this.getArguments().set(1, ratio);
			
			return this;
		}
		
		@Override
		public final PercentileMask autoShape() {
			final int[] inputsShape = this.getInputs().getShape();
			
			checkLength(2, inputsShape.length);
			
			return this.setShape(inputsShape);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> inputs = this.getInputs();
			final Node<?> ratio = this.getRatio();
			final int n = inputs.getShape()[1];
			final Node<?> ith = $(ROUND, $(ratio, "*", n - 1));
			
			return $(KRONECKER, sortIndices(inputs), ith).setStorage(this);
		}
		
		private static final long serialVersionUID = -3725650903059947346L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-04)
	 */
	public static final class Percentile extends CustomNode<Percentile> {
		
		public Percentile() {
			super(Arrays.asList(new Node[2]));
		}
		
		public final Node<?> getInputs() {
			return this.getArguments().get(0);
		}
		
		public final Percentile setInputs(final Node<?> inputs) {
			this.getArguments().set(0, inputs);
			
			return this;
		}
		
		public final Node<?> getRatio() {
			return this.getArguments().get(1);
		}
		
		public final Percentile setRatio(final Node<?> ratio) {
			this.getArguments().set(1, ratio);
			
			return this;
		}
		
		@Override
		public final Percentile autoShape() {
			final int[] inputsShape = this.getInputs().getShape();
			
			checkLength(2, inputsShape.length);
			
			return this.setShape(inputsShape[0], 1);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> inputs = this.getInputs();
			final Node<?> ratio = this.getRatio();
			final int n = inputs.getShape()[1];
			
			return sum($(inputs, "*", percentileMask(inputs, ratio)), 1, n).setStorage(this);
		}
		
		private static final long serialVersionUID = -3725650903059947346L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-10)
	 */
	public static final class Ones extends CustomNode<Ones> {
		
		private final int[] shape;
		
		public Ones(final int... shape) {
			this.shape = shape;
		}
		
		@Override
		public final Ones autoShape() {
			return this.setShape(this.shape);
		}
		
		@Override
		protected final Node<?> doUnfold() {
			final Node<?> result = new Data().setStorage(this);
			final int n = result.getLength();
			
			for (int i = 0; i < n; ++i) {
				result.set(i, 1F);
			}
			
			return result;
		}
		
		private static final long serialVersionUID = 4095941223149887763L;
		
	}
	
}
