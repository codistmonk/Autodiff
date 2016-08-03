package autodiff.learning;

import static autodiff.computing.Functions.EXP;
import static autodiff.computing.Functions.LN;
import static autodiff.nodes.NodesTools.SUM;
import static autodiff.nodes.NodesTools.$;
import static autodiff.nodes.NodesTools.shape;

import autodiff.computing.NodeProcessor;
import autodiff.io.LabeledData;
import autodiff.nodes.Node;

import java.util.HashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.DoubleSupplier;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-22)
 */
public final class LearningTools {
	
	private LearningTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final Node<?> newCrossEntropyClassificationLoss(final Node<?> y, final Node<?> labels) {
		final int classCount = y.getLength() / labels.getLength();
		final Node<?> exp = $(EXP, y);
		final Node<?> denom = $(SUM, new int[] { classCount }, exp);
		final Node<?> num = $(exp, "@", shape(labels, labels.getLength(), 1));
//		final Node<?> num = $(exp, "@", labels.setShape(labels.getLength(), 1));
		final Node<?> softmax = $(num, "/", denom);
		
		return $("-", $($(SUM, $(LN, softmax)), "/", softmax.getLength()));
	}
	
	public static final ConfusionMatrix<Integer> evaluate(final Node<?> y, final LabeledData testData, final LabeledData minibatchData, final NodeProcessor processor) {
		final ConfusionMatrix<Integer> result = new ConfusionMatrix<>();
		final MinibatchContext minibatchContext = new MinibatchContext(testData, minibatchData);
		final int n = y.getLength();
		final int classCount = n / minibatchData.getItemCount();
		final int[] done = { 0 };
		
		minibatchContext.forEachMinibatch(() -> {
			processor.fullForward(y);
			
			for (int i = 0, j = 0; i < n && done[0] < testData.getItemCount(); i += classCount, ++j, ++done[0]) {
				result.count(argmax(y, i, i + classCount), (int) minibatchData.getLabels().get(j));
			}
		});
		
		return result;
	}
	
	public static final int argmax(final Node<?> node, final int begin, final int end) {
		float max = Float.NEGATIVE_INFINITY;
		int result = -1;
		
		for (int i = begin; i < end; ++i) {
			final float value = node.get(i);
			
			if (max < value) {
				max = value;
				result = i - begin;
			}
		}
		
		return result;
	}
	
	public static final void initialize(final DoubleSupplier f, final Node<?>... nodes) {
		for (final Node<?> node : nodes) {
			final int n = node.getLength();
			
			for (int i = 0; i < n; ++i) {
				node.set(i, (float) f.getAsDouble());
			}
		}
	}
	
	public static final Float[] packLabels(final Node<?> labels) {
		final Float[] result = toSortedSet(labels).toArray(new Float[0]);
		final Map<Float, Integer> map = new HashMap<>();
		
		for (int i = 0; i < result.length; ++i) {
			map.put(result[i], i);
		}
		
		final int n = labels.getLength();
		
		for (int i = 0; i < n; ++i) {
			labels.set(i, map.get(labels.get(i)));
		}
		
		return result;
	}

	public static final SortedSet<Float> toSortedSet(final Node<?> labels) {
		final SortedSet<Float> values = new TreeSet<>();
		final int n = labels.getLength();
		
		for (int i = 0; i < n; ++i) {
			values.add(labels.get(i));
		}
		return values;
	}
	
}
