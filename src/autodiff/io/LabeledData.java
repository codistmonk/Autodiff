package autodiff.io;

import static java.lang.Math.ceil;
import static multij.tools.Tools.array;

import java.io.Serializable;
import java.util.Random;

import autodiff.nodes.Data;
import autodiff.nodes.Node;

/**
 * @author codistmonk (creation 2016-07-16)
 */
public final class LabeledData implements Serializable {
	
	private final Node<?> inputs;
	
	private final Node<?> labels;
	
	public LabeledData(final Node<?> inputs, final Node<?> labels) {
		this.inputs = inputs;
		this.labels = labels;
	}
	
	public final Node<?> getInputs() {
		return this.inputs;
	}
	
	public final Node<?> getLabels() {
		return this.labels;
	}
	
	public final int getInputCount() {
		return this.getLabels().getLength();
	}
	
	public final int getInputLength() {
		return this.getInputs().getLength() / this.getInputCount();
	}
	
	public final void shuffle(final Random random) {
		final int n = this.getInputCount();
		
		for (int i = 0; i < n; ++i) {
			this.swap(i, random.nextInt(n));
		}
	}
	
	public final void swap(final int i, final int j) {
		final int inputLength = this.getInputLength();
		final int offsetI = i * inputLength;
		final int offsetJ = j * inputLength;
		
		for (int k = 0; k < inputLength; ++k) {
			swap(this.getInputs(), offsetI + k, offsetJ + k);
		}
		
		swap(this.getLabels(), i, j);
	}
	
	public final LabeledData[] split(final double ratio) {
		final int n = this.getInputCount();
		final int m = (int) ceil(n * ratio);
		
		return array(this.slice(0, m), this.slice(m, n));
	}
	
	public final LabeledData slice(final int begin, final int end) {
		return new LabeledData(
				slice(this.getInputs(), this.getInputLength(), begin, end),
				slice(this.getLabels(), 1, begin, end));
	}
	
	private static final long serialVersionUID = -3272274112365487159L;
	
	public static final void swap(final Node<?> node, final int i, final int j) {
		final float tmp = node.get(i);
		node.set(i, node.get(j));
		node.set(j, tmp);
	}
	
	public static final Node<?> slice(final Node<?> node, final int itemLength, final int begin, final int end) {
		final int[] resultShape = node.getShape().clone();
		resultShape[0] = end - begin;
		final Node<?> result = new Data().setShape(resultShape);
		
		for (int i = begin; i < end; ++i) {
			for (int j = 0; j < itemLength; ++j) {
				result.set(j + itemLength * (i - begin), node.get(j + itemLength * i));
			}
		}
		
		return result;
	}
	
}
