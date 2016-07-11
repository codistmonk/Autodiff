package autodiff.processors;

import static java.lang.Math.max;
import static java.lang.Math.min;
import static java.util.Collections.reverse;

import autodiff.nodes.Convolution2D;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.MaxPooling2D;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Selection;
import autodiff.nodes.Sum;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

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
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public final Void visit(final MaxPooling2D node) {
			final Node<?> argument = node.getArgument();
			final int[] argumentShape = argument.getShape();
			final int inputHeight = argumentShape[argumentShape.length - 2];
			final int inputWidth = argumentShape[argumentShape.length - 1];
			final int offsetX = node.getOffsetX();
			final int offsetY = node.getOffsetY();
			final int strideX = node.getStrideX();
			final int strideY = node.getStrideY();
			final int kernelWidth = node.getKernelWidth();
			final int kernelHeight = node.getKernelHeight();
			final int hh = (kernelHeight - 1) / 2;
			final int hw = (kernelWidth - 1) / 2;
			final int inputSize = inputWidth * inputHeight;
			final int inputCount = argument.getLength() / inputSize; 
			
			for (int i = 0, j = 0; i < inputCount; ++i) {
				for (int y = offsetY; y < inputHeight; y += strideY) {
					final int top = max(0, y - hh);
					final int bottomEnd = min(top + kernelHeight, inputHeight);
					
					for (int x = offsetX; x < inputWidth; x += strideX, ++j) {
						final int left = max(0, x - hw);
						final int rightEnd = min(left + kernelWidth, inputWidth);
						float value = Float.NEGATIVE_INFINITY;
						
						for (int yy = top; yy < bottomEnd; ++yy) {
							for (int xx = left; xx < rightEnd; ++xx) {
								final float inputValue = argument.get(xx + inputWidth * yy + inputSize * i);
								
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
		
		private static final long serialVersionUID = -8842155630294708599L;
		
		public static final Forwarder INSTANCE = new Forwarder();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-11)
	 */
	public static final class BackwardDiffer implements NodeVisitor<Void> {
		
		private static final long serialVersionUID = -2003909030537706641L;
		
		public static final BackwardDiffer INSTANCE = new BackwardDiffer();
		
	}
	
}
