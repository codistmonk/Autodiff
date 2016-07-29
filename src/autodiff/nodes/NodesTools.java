package autodiff.nodes;

import static autodiff.computing.Functions.INFIX_OPERATORS;
import static autodiff.computing.Functions.KRONECKER;
import static autodiff.computing.Functions.POSTFIX_OPERATORS;
import static autodiff.computing.Functions.PREFIX_OPERATORS;
import static autodiff.computing.Functions.SUM;
import static multij.tools.Tools.*;

import java.util.Arrays;
import java.util.function.Supplier;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-15)
 */
public final class NodesTools {
	
	private NodesTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final int LEFT_OFFSET = 0;
	
	public static final int RIGHT_OFFSET = 1;
	
	public static final int TOP_OFFSET = 2;
	
	public static final int BOTTOM_OFFSET = 3;
	
	public static final int HORIZONTAL_STRIDE = 0;
	
	public static final int VERTICAL_STRIDE = 1;
	
	/**
	 * Not an Index.
	 */
	public static final float NaI = -Integer.MAX_VALUE;
	
	public static final Node<?> patches(final Node<?> inputs, final int[] offsets, final int[] strides, final int[] patchShape) {
		final int[] inputsShape = inputs.getShape();
		final int inputWidth = inputsShape[inputsShape.length - 1];
		final int inputHeight = inputsShape[inputsShape.length - 2];
		final int inputChannels = inputsShape[inputsShape.length - 3];
		final int patchWidth = patchShape[patchShape.length - 1];
		final int patchHeight = patchShape[patchShape.length - 2];
		final int outputWidth = (inputWidth - offsets[LEFT_OFFSET] - offsets[RIGHT_OFFSET] + strides[HORIZONTAL_STRIDE] - 1) / strides[HORIZONTAL_STRIDE];
		final int outputHeight = (inputHeight - offsets[TOP_OFFSET] - offsets[BOTTOM_OFFSET] + strides[VERTICAL_STRIDE] - 1) / strides[VERTICAL_STRIDE];
		final int patchSize = patchWidth * patchHeight;
		final int outputSize = outputWidth * outputHeight;
		final int inputSize = inputWidth * inputHeight;
		final int inputCount = inputs.getLength() / inputSize;
		final Node<?> indices = new Data().setShape(1, patchSize * outputSize);
		
		for (int c = 0; c < inputChannels; ++c) {
			for (int y = offsets[TOP_OFFSET], o = 0; y < inputHeight - offsets[BOTTOM_OFFSET]; y += strides[VERTICAL_STRIDE]) {
				for (int x = offsets[LEFT_OFFSET]; x < inputWidth - offsets[RIGHT_OFFSET]; x += strides[HORIZONTAL_STRIDE]) {
					for (int i = 0; i < patchHeight; ++i) {
						final int yy = y - (patchHeight - 1) / 2 + i;
						
						for (int j = 0; j < patchWidth; ++j, ++o) {
							final int xx = x - (patchWidth - 1) / 2 + j;
							
							if (0 <= yy && yy < inputHeight && 0 <= xx && xx < inputWidth) {
								indices.set(o, xx + inputWidth * (yy + inputHeight * c));
							} else {
								indices.set(o, NaI);
							}
						}
					}
				}
			}
		}
		
		return shape(selection(shape(inputs, inputCount, inputSize), indices), inputCount * outputSize, 1, patchHeight, patchWidth);
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
		
		final Node<?> shift = new Zipping().setFunctionName("+").setLeft(indices).setRight(shiftData).autoShape();
		final Node<?> replicationMatrix = new Data().setShape(indicesStride, indicesStride * vectorsStride);
		
		for (int i = 0; i < indicesStride; ++i) {
			for (int j = 0; j < vectorsStride; ++j) {
				replicationMatrix.set(j + (indicesStride + 1) * vectorsStride * i, 1);
			}
		}
		
		final Node<?> replicatedIndices = new MatrixMultiplication()
		.setLeft(shape(shift, indices.getLength() / indicesStride, indicesStride))
		.setRight(replicationMatrix).autoShape();
		final Node<?> range = new Data().setShape(vectorsStride);
		
		for (int i = 0; i < vectorsStride; ++i) {
			range.set(i, i);
		}
		
		final Node<?> mask = new Zipping().setFunctionName(KRONECKER).setLeft(replicatedIndices).setRight(range).autoShape();
		
		return shape(new MatrixMultiplication()
		.setLeft(shape(vectors, vectors.getLength() / vectorsStride, vectorsStride))
		.setRight(shape(mask, mask.getLength() / vectorsStride, vectorsStride))
		.setTransposeRight(true)
		.autoShape(), resultShape);
//		return shape(sum(new Zipping().setFunctionName("*").setLeft(vectors).setRight(mask).autoShape(), vectorsStride), resultShape);
	}
	
	public static final Node<?> sum(final Node<?> argument, final int... strides) {
		if (strides.length == 0) {
			final int n = argument.getLength();
			
			return shape(new MatrixMultiplication().setLeft(shape(argument, 1, n)).setRight(ones(n, 1)).autoShape(), 1);
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
		
		return shape(new MatrixMultiplication().setLeft(shape(argument, 1, m)).setRight(right).autoShape(), resultShape);
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
	
	public static void checkLength(final int expectedLength, final int actualLength) {
		check(expectedLength == actualLength, () -> "Expected length: " + expectedLength + ", actual: " + actualLength);
	}
	
	public static void check(final boolean b, final Supplier<String> errorMessage) {
		if (!b) {
			throw new RuntimeException(errorMessage.get());
		}
	}
	
	public static int product(final int... values) {
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
		
		if (n == 3) {
			if (INFIX_OPERATORS.contains(objects[1])) {
				return new Zipping().setLeft($(objects[0])).setRight($(objects[2])).setFunctionName(objects[1].toString()).autoShape();
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
	
}
