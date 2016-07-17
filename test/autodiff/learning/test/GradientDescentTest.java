package autodiff.learning.test;

import static autodiff.computing.Functions.COS;
import static autodiff.computing.Functions.EXP;
import static autodiff.computing.Functions.LN;
import static autodiff.computing.Functions.SQMINUS;
import static autodiff.computing.Functions.SQUARED;
import static autodiff.computing.Functions.SUM;
import static autodiff.computing.Functions.TIMES;
import static autodiff.nodes.NodesTools.$;
import static java.lang.Math.min;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.debugPrint;
import static org.junit.Assert.*;

import autodiff.computing.DefaultProcessor;
import autodiff.computing.NodeProcessor;
import autodiff.io.Iris;
import autodiff.io.LabeledData;
import autodiff.learning.AbstractMinimizer;
import autodiff.learning.ConfusionMatrix;
import autodiff.learning.GradientDescent;
import autodiff.learning.Minimizer;
import autodiff.nodes.Data;
import autodiff.nodes.Mapping;
import autodiff.nodes.Node;
import autodiff.nodes.Zipping;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.DoubleSupplier;

import org.junit.Test;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public final class GradientDescentTest {
	
	@Test
	public final void test1() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $(x, SQUARED);
		final GradientDescent gd = new GradientDescent(y).setIterations(100);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, x.get(), 1.0E-4);
		assertEquals(0.0, y.get(), 1.0E-4);
	}
	
	@Test
	public final void test2() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $($(x, SQUARED), "-", $(COS, $(8, TIMES, x)));
		final GradientDescent gd = new GradientDescent(y).setIterations(50).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, x.get(), 1.0E-4);
		assertEquals(-1.0, y.get(), 1.0E-4);
	}
	
	@Test
	public final void test3() {
		final Random random = new Random(2L);
		final Node<?> m = new Data().setShape(2, 2).set(
				1F, 2F,
				2F, 1F);
		final Node<?> v = new Data().setShape(2, 2).set(
				random.nextFloat(), random.nextFloat(),
				random.nextFloat(), random.nextFloat());
		final Node<?> k = new Data().setShape(1, 2).set(
				random.nextFloat(), random.nextFloat());
		final Node<?> mv = $(m, v);
		final Node<?> vk = $(v, ".*", k);
		final Node<?> vSquared = $(v, SQUARED);
		final Node<?> v2 = $(SUM, new int[] { 2, 1 }, vSquared);
		final Node<?> lengthConstraint = $(SUM, $(v2, SQMINUS, $(1F, 1F)));
		final Node<?> colinearityConstraint = $(SUM, $(mv, SQMINUS, vk));
		final Node<?> orthogonalityConstraint = $($($(v, "@", $(0, 0)).setShape(1, 2), $(v, "@", $(1, 1)).setShape(2, 1)), SQUARED);
		final Node<?> w = $(1, 1, 1.63);
		final Node<?> z = $($($(w, "@", 0), ".*", colinearityConstraint), "+", $($($(w, "@", 1), ".*", orthogonalityConstraint), "+", $($(w, "@", 2), ".*", lengthConstraint)));
		final GradientDescent gd = new GradientDescent(z).setIterations(200).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
		gd.getParameters().add(v);
		gd.getParameters().add(k);
		gd.run();
		
		Tools.debugPrint(m);
		Tools.debugPrint(v);
		Tools.debugPrint(k);
		Tools.debugPrint(z);
		Tools.debugPrint(colinearityConstraint, orthogonalityConstraint, lengthConstraint);
		
		assertArrayEquals(new float[] { 3F, -1F }, k.get(new float[k.getLength()]), 1E-4F);
		assertEquals(0.0, z.get(), 1.0E-4);
	}
	
	@Test
	public final void testIris1() {
		final Random random = new Random(2L);
		final LabeledData allData = Iris.getIrisData();
		final Float[] classIds = packLabels(allData.getLabels());
		
		allData.shuffle(random);
		
		final LabeledData[] split = allData.split(2.0 / 3.0);
		final LabeledData trainingData = split[0];
		final LabeledData testData = split[1];
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.length;
		
		final Node<?> x = trainingData.getInputs();
		final Node<?> a = new Data().setShape(inputLength, classCount);
		final Node<?> b = new Data().setShape(classCount);
		final Node<?> y = $($(x, a), "+", b);
		final Node<?> cost = newCrossEntropyClassificationLoss(y, trainingData.getLabels());
		
		initialize(random::nextGaussian, a, b);
		
		{
			this.getProcessor().fullForward(cost);
			
			debugPrint(cost.get());
		}
		
		final GradientDescent gd = new GradientDescent(cost).setLearningRate(1E-1F).setIterations(400);
		gd.getParameters().add(a);
		gd.getParameters().add(b);
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, trainingData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate($($(testData.getInputs(), a), "+", b), testData, testData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.getCounts(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy());
			debugPrint(testData.getItemCount(), testResult.getCounts(), testResult.computeMacroF1(), testResult.computeAccuracy());
		}
		
		gd.run();
		
		{
			this.getProcessor().fullForward(cost);
			
			debugPrint(cost.get());
		}
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, trainingData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate($($(testData.getInputs(), a), "+", b), testData, testData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.getCounts(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy());
			debugPrint(testData.getItemCount(), testResult.getCounts(), testResult.computeMacroF1(), testResult.computeAccuracy());
			
			assertTrue(0.98 <= testResult.computeAccuracy());
		}
	}
	
	public static final List<?> toTree(final Node<?> node) {
		final List<Object> result = new ArrayList<>();
		
		result.add(node.getClass().getSimpleName());
		
		final Mapping mapping = cast(Mapping.class, node);
		
		if (mapping != null) {
			result.add(mapping.getFunctionName());
		}
		
		final Zipping zipping = cast(Zipping.class, node);
		
		if (zipping != null) {
			result.add(zipping.getFunctionName());
		}
		
		node.getArguments().forEach(n -> result.add(toTree(n)));
		
		return result;
	}
	
	@Test
	public final void testIris2() {
		final Random random = new Random(2L);
		final LabeledData allData = Iris.getIrisData();
		final Float[] classIds = packLabels(allData.getLabels());
		
		allData.shuffle(random);
		
		final LabeledData[] split = allData.split(2.0 / 3.0);
		final LabeledData trainingData = split[0];
		final LabeledData testData = split[1];
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.length;
//		final int minibatchSize = trainingData.getItemCount();
		final int minibatchSize = 40;
		final LabeledData minibatchData = new LabeledData(minibatchSize, inputLength);
		
		final Node<?> x = minibatchData.getInputs();
		final Node<?> a = new Data().setShape(inputLength, classCount);
		final Node<?> b = new Data().setShape(classCount);
		final Node<?> y = $($(x, a), "+", b);
		final Node<?> cost = newCrossEntropyClassificationLoss(y, minibatchData.getLabels());
		
		initialize(random::nextGaussian, a, b);
		
		final GradientDescent gd = new GradientDescent(cost).setIterations(1);
		gd.getParameters().add(a);
		gd.getParameters().add(b);
		final MinibatchMinimizer minibatchMinimizer = new MinibatchMinimizer(gd, trainingData, minibatchData).setEpochs(100);
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.getCounts(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy());
			debugPrint(testData.getItemCount(), testResult.getCounts(), testResult.computeMacroF1(), testResult.computeAccuracy());
		}
		
		minibatchMinimizer.run();
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.getCounts(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy());
			debugPrint(testData.getItemCount(), testResult.getCounts(), testResult.computeMacroF1(), testResult.computeAccuracy());
			
			assertTrue(0.98 <= testResult.computeAccuracy());
		}
	}
	
	public final NodeProcessor getProcessor() {
		return DefaultProcessor.INSTANCE;
	}
	
	public static final Node<?> newCrossEntropyClassificationLoss(final Node<?> y, final Node<?> labels) {
		final int classCount = y.getLength() / labels.getLength();
		final Node<?> exp = $(EXP, y);
		final Node<?> denom = $(SUM, new int[] { classCount }, exp);
		final Node<?> num = $(exp, "@", labels);
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
	
	/**
	 * @author codistmonk (creation 2016-07-16)
	 */
	public static final class MinibatchContext implements Serializable {
		
		private final LabeledData sourceData;
		
		private final LabeledData minibatchData;
		
		public MinibatchContext(final LabeledData sourceData, final LabeledData minibatchData) {
			this.sourceData = sourceData;
			this.minibatchData = minibatchData;
		}
		
		public final LabeledData getSourceData() {
			return this.sourceData;
		}
		
		public final LabeledData getMinibatchData() {
			return this.minibatchData;
		}
		
		public final void forEachMinibatch(final Runnable command) {
			final int m = this.getSourceData().getItemCount();
			final int n = this.getMinibatchData().getItemCount();
			
			for (int i = 0; i < m; i += n) {
				this.getSourceData().copy(i, min(i + n, m - i), this.getMinibatchData(), 0);
				command.run();
			}
		}
		
		private static final long serialVersionUID = -4327393127426597114L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-16)
	 */
	public static final class MinibatchMinimizer extends AbstractMinimizer<MinibatchMinimizer> {
		
		private final Minimizer<?> iterationMinimizer;
		
		private final MinibatchContext minibatchContext;
		
		private int epochs;
		
		private int currentEpoch;
		
		public MinibatchMinimizer(final Minimizer<?> iterationMinimizer, final LabeledData trainingData, final LabeledData minibatchData) {
			super(iterationMinimizer.getCost());
			this.iterationMinimizer = iterationMinimizer;
			this.minibatchContext = new MinibatchContext(trainingData, minibatchData);
			this.epochs = 10;
			
			this.setProcessor(iterationMinimizer.getProcessor());
			
			iterationMinimizer.setSavingBestParameters(false);
		}
		
		public final Minimizer<?> getIterationMinimizer() {
			return this.iterationMinimizer;
		}
		
		public final MinibatchContext getMinibatchContext() {
			return this.minibatchContext;
		}
		
		public final int getEpochs() {
			return this.epochs;
		}
		
		public final int getCurrentEpoch() {
			return this.currentEpoch;
		}
		
		public final MinibatchMinimizer setEpochs(final int epochs) {
			this.epochs = epochs;
			
			return this;
		}
		
		@Override
		public final void run() {
			this.getParameters().clear();
			this.getParameters().addAll(this.getIterationMinimizer().getParameters());
			this.getParameterLocks().clear();
			this.getParameterLocks().putAll(this.getIterationMinimizer().getParameterLocks());
			this.currentEpoch = 0;
			
			super.run();
		}
		
		@Override
		public final boolean isDone() {
			return this.getEpochs() <= ++this.currentEpoch;
		}
		
		@Override
		public final void updateParameters() {
			this.getMinibatchContext().forEachMinibatch(this.getIterationMinimizer());
		}
		
		@Override
		public final float updateCost(final float previousBestCost) {
			final float[] cost = { 0F };
			
			this.getMinibatchContext().forEachMinibatch(() -> {
				cost[0] += this.getProcessor().fullForward(this.getCost()).get();
			});
			
			if (cost[0] < previousBestCost) {
				this.saveBestParameters();
				
				return cost[0];
			}
			
			return previousBestCost;
		}
		
		private static final long serialVersionUID = 1342716574795573640L;
		
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
