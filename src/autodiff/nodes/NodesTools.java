package autodiff.nodes;

import static autodiff.computing.Functions.INFIX_OPERATORS;
import static autodiff.computing.Functions.KRONECKER;
import static autodiff.computing.Functions.POSTFIX_OPERATORS;
import static autodiff.computing.Functions.PREFIX_OPERATORS;
import static autodiff.computing.Functions.STEP1;
import static java.lang.Math.round;
import static multij.tools.Tools.*;
import autodiff.computing.DefaultProcessor;

import java.io.Serializable;
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
	
	static final AtomicLong nextId = new AtomicLong();
	
	public static final Node<?> sortIndices(final Node<?> inputs) {
		final int[] shape = inputs.getShape();
		
		checkLength(2, shape.length);
		
		final int n = shape[1];
		
		final Node<?> replicationMatrix1 = new Data().setShape(n, n * n);
		final Node<?> replicationMatrix2 = new Data().setShape(n, n * n);
		
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < n; ++j) {
				replicationMatrix1.set(j + (n * n + n) * i, 1F);
			}
		}
		
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < n; ++j) {
				replicationMatrix2.set(i + j * n + n * n * i, 1F);
			}
		}
		
		final Node<?> replicated1 = $(inputs, replicationMatrix1);
		final Node<?> replicated2 = $(inputs, replicationMatrix2);
		final Node<?> difference = $(replicated1, "-", replicated2);
		final Node<?> greaterness = $(STEP1, difference);
		final Node<?> equality = $(KRONECKER, replicated1, replicated2);
		final Node<?> indexGreaterness = new Data().setShape(1, n * n);
		
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < i; ++j) {
				indexGreaterness.set(j + n * i, 1F);
			}
		}
		
		final Node<?> aboveness = $(greaterness, "+", $(equality, "*", indexGreaterness));
		
		return sum(aboveness, 1, n);
	}
	
	public static final Node<?> percentileMask(final Node<?> inputs, final float ratio) {
		final int n = inputs.getShape()[1];
		final Node<?> ith = new Data().setShape(n);
		
		DefaultProcessor.INSTANCE.fill(ith, round(ratio * (n - 1)));
		
		return $(KRONECKER, sortIndices(inputs), ith);
	}
	
	public static final Node<?> percentile(final Node<?> inputs, final float ratio) {
		final int n = inputs.getShape()[1];
		
		return sum($(inputs, "*", percentileMask(inputs, ratio)), 1, n);
	}
	
	public static final Node<?> maxPooling(final Node<?> inputs, final int[] offsets, final int[] strides, final int[] kernelShape) {
		final GridSampling grid = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		final Node<?> patches = patches(inputs, new PatchSampling(grid).setPatchShape(kernelShape));
		final int[] patchesShape = patches.getShape();
		
		return shape(percentile(shape(patches, patchesShape[0] * patchesShape[1], patchesShape[2] * patchesShape[3]), 1F),
				grid.getInputCount(), grid.getInputChannels(), grid.getOutputHeight(), grid.getOutputWidth());
	}
	
	public static final Node<?> convolution(final Node<?> inputs, final int[] offsets, final int[] strides, final Node<?> kernel) {
		final GridSampling grid = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		final Node<?> patches = patches(inputs, new PatchSampling(grid).setPatchShape(kernel.getShape()));
		final int kernelLength = kernel.getLength();
		
		return shape($(
				shape(patches, patches.getLength() / kernelLength, kernel.getLength()),
				shape(kernel, kernel.getLength(), 1)),
				grid.getInputCount(), 1, grid.getOutputHeight(), grid.getOutputWidth());
	}
	
	public static final Node<?> patches(final Node<?> inputs, final int[] offsets, final int[] strides, final int[] patchShape) {
		final GridSampling grid = new GridSampling().setInputsShape(inputs.getShape()).setOffsets(offsets).setStrides(strides);
		
		return patches(inputs, new PatchSampling(grid).setPatchShape(patchShape));
	}
	
	public static final Node<?> patches(final Node<?> inputs, final PatchSampling patch) {
		final GridSampling grid = patch.getSampling();
		final int inputWidth = grid.getInputWidth();
		final int inputHeight = grid.getInputHeight();
		final int inputChannels = grid.getInputChannels();
		final int outputSize = grid.getOutputSize();
		final int inputSize = grid.getInputSize();
		final int inputCount = grid.getInputCount();
		final int patchWidth = patch.getPatchWidth();
		final int patchHeight = patch.getPatchHeight();
		final int patchSize = patch.getPatchSize();
		final Node<?> indices = new Data().setShape(1, patchSize * outputSize);
		
		{
			final int[] o = { 0 };
			
			grid.forEach(centerPixel -> {
				patch.forEachPixelAround(centerPixel, p -> {
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
		
		return shape(selection(shape(inputs, inputCount, inputSize), indices),
				inputCount * outputSize, inputChannels, patchHeight, patchWidth);
	}
	
	public static final Node<?> selection(final Node<?> vectors, final Node<?> indices) {
		final int[] vectorsShape = vectors.getLengths(new int[2]);
		final int[] indicesShape = indices.getLengths(new int[2]);
		final int indicesStride = indicesShape[1];
		final int vectorsStride = vectorsShape[1] * indicesShape[0];
		final int m = vectors.getLength() / vectorsStride;
		final int n = indices.getLength();
		final int[] resultShape = { m, n };
		
		final Node<?> shiftData = new Data().setShape(indices.getLength());
		
		for (int i = 1; i < indicesShape[0]; ++i) {
			for (int j = 0; j < indicesShape[1]; ++j) {
				shiftData.set(j + indicesShape[1] * i, vectorsShape[1] * i);
			}
		}
		
		final Node<?> shift = $(indices, "+", shiftData);
		final Node<?> replicationMatrix = new Data().setShape(indicesStride, indicesStride * vectorsStride);
		
		for (int i = 0; i < indicesStride; ++i) {
			for (int j = 0; j < vectorsStride; ++j) {
				replicationMatrix.set(j + (indicesStride + 1) * vectorsStride * i, 1);
			}
		}
		
		final Node<?> replicatedIndices = $(shape(shift, indices.getLength() / indicesStride, indicesStride), replicationMatrix);
		final Node<?> range = newRange(vectorsStride);
		final Node<?> mask = $(KRONECKER, replicatedIndices, range);
		
		return shape($(shape(vectors, vectors.getLength() / vectorsStride, vectorsStride),
				shape(mask, mask.getLength() / vectorsStride, vectorsStride), T), resultShape);
	}
	
	public static final Node<?> newRange(final int n) {
		final Node<?> result = new Data().setShape(n);
		
		for (int i = 0; i < n; ++i) {
			result.set(i, i);
		}
		
		return result;
	}
	
	public static final Node<?> sum(final Node<?> argument, final int... strides) {
		if (strides.length == 0) {
			final int n = argument.getLength();
			
			return shape($(shape(argument, 1, n), ones(n, 1)), 1);
		}
		
		final int[] resultShape = argument.getLengths(new int[strides.length]);
		
		for (int i = 0; i < strides.length; ++i) {
			if (resultShape[i] % strides[i] != 0) {
				throw new IllegalArgumentException(resultShape[i] + " not divisible by " + strides[i]);
			}
			
			resultShape[i] /= strides[i];
		}
		
		final int m = argument.getLength();
		final int n = product(resultShape);
		final Node<?> right = new Data().setShape(m, n);
		final int[] argumentShape = argument.getLengths(new int[strides.length]);
		final int[] outerBounds = bounds(resultShape);
		final int[] innerBounds = bounds(strides);
		
		for (final int[] i : cartesian(outerBounds)) {
			for (int j = 0; j < i.length; ++j) {
				innerBounds[2 * j + 0] = i[j] * strides[j];
				innerBounds[2 * j + 1] = i[j] * strides[j] + strides[j] - 1;
			}
			
			final int outputIndex = indexFromCartesian(resultShape, i);
			
			for (final int[] j : cartesian(innerBounds)) {
				final int k = indexFromCartesian(argumentShape, j);
				
				right.set(outputIndex + n * k, 1F);
			}
		}
		
		return shape($(shape(argument, 1, m), right), resultShape);
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
		return Arrays.equals(node.getShape(), shape) ? node : new ShapeNode(node).setShape(shape);
	}
	
	public static final Node<?> ones(final int... shape) {
		final Node<?> result = new Data().setShape(shape);
		final int n = result.getLength();
		
		for (int i = 0; i < n; ++i) {
			result.set(i, 1F);
		}
		
		return result;
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
		return Arrays.stream(values).reduce((x, y) -> x * y).getAsInt();
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
	
}
