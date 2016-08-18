package autodiff.learning.test;

import static autodiff.computing.Functions.COS;
import static autodiff.computing.Functions.SQMINUS;
import static autodiff.computing.Functions.SQUARED;
import static autodiff.learning.LearningTools.*;
import static autodiff.nodes.NodesTools.SUM;
import static autodiff.nodes.NodesTools.$;
import static multij.tools.Tools.DEBUG_STACK_OFFSET;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.debug;
import static multij.tools.Tools.debugPrint;
import static org.junit.Assert.*;

import autodiff.computing.NodeProcessor;
import autodiff.io.Iris;
import autodiff.io.LabeledData;
import autodiff.learning.ConfusionMatrix;
import autodiff.learning.GradientDescent;
import autodiff.learning.MinibatchMinimizer;
import autodiff.nodes.Data;
import autodiff.nodes.Mapping;
import autodiff.nodes.Node;
import autodiff.nodes.Zipping;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.stream.Collectors;

import multij.tools.TicToc;
import multij.tools.Tools;

import org.junit.Test;

/**
 * @author codistmonk (creation 2016-07-14)
 */
public abstract class GradientDescentTest {
	
	protected GradientDescentTest() {
		// NOP
	}
	
	@Test
	public final void test1() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $(x, SQUARED);
		final GradientDescent gd = new GradientDescent(y).setProcessor(this.getProcessor()).setIterations(100);
		
		gd.getParameters().add(x);
		gd.run();
		
		assertEquals(0.0, x.get(), 1.0E-4);
		assertEquals(0.0, y.get(), 1.0E-4);
	}
	
	@Test
	public final void test2() {
		final Random random = new Random(1L);
		final Node<?> x = new Data().set(random.nextFloat() * 100F);
		final Node<?> y = $($(x, SQUARED), "-", $(COS, $(8, "*", x)));
		final GradientDescent gd = new GradientDescent(y).setProcessor(this.getProcessor()).setIterations(50).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
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
		final Node<?> vk = $(v, "*", k);
		final Node<?> vSquared = $(v, SQUARED);
		final Node<?> v2 = $(SUM, new int[] { 2, 1 }, vSquared);
		final Node<?> lengthConstraint = $(SUM, $(v2, SQMINUS, $(1F, 1F)));
		final Node<?> colinearityConstraint = $(SUM, $(mv, SQMINUS, vk));
		final Node<?> orthogonalityConstraint = $($($(v, "@", $(0, 0).shaped(2, 1)).shaped(1, 2), $(v, "@", $(1, 1).shaped(2, 1)).shaped(2, 1)), SQUARED);
		final Node<?> w = $(1, 1, 1.63).setShape(1, 3);
		final Node<?> w0 = $(w, "@", 0);
		final Node<?> w1 = $(w, "@", 1);
		final Node<?> w2 = $(w, "@", 2);
		final Node<?> z = $($(w0, "*", colinearityConstraint), "+", $($(w1, "*", orthogonalityConstraint), "+", $(w2, "*", lengthConstraint)));
		final GradientDescent gd = new GradientDescent(z).setProcessor(this.getProcessor()).setIterations(200).setLearningRateDivisor(1.5F).setLearningRateMultiplier(1.05F);
		
		gd.getParameters().add(v);
		gd.getParameters().add(k);
		gd.run();
		
		Tools.debugPrint(w0, w1, w2);
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
		final Map<Float, Integer> classIds = toIndexMap(allData.getLabels());
		
		packLabels(allData.getLabels(), classIds);
		
		allData.shuffle(random);
		
		final LabeledData[] split = allData.split(2.0 / 3.0);
		final LabeledData trainingData = split[0];
		final LabeledData testData = split[1];
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.size();
		
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
		
		final GradientDescent gd = new GradientDescent(cost).setProcessor(this.getProcessor()).setLearningRate(1E-1F).setIterations(400);
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
		
		printTimers(this.getProcessor().getTimers());
	}
	
	@Test
	public final void testIris2() {
		final Random random = new Random(2L);
		final LabeledData allData = Iris.getIrisData();
		final Map<Float, Integer> classIds = toIndexMap(allData.getLabels());
		
		packLabels(allData.getLabels(), classIds);
		
		allData.shuffle(random);
		
		final LabeledData[] split = allData.split(2.0 / 3.0);
		final LabeledData trainingData = split[0];
		final LabeledData testData = split[1];
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.size();
//		final int minibatchSize = trainingData.getItemCount();
		final int minibatchSize = 40;
		final LabeledData minibatchData = new LabeledData(minibatchSize, inputLength);
		
		final Node<?> x = minibatchData.getInputs();
		final Node<?> a = new Data().setShape(inputLength, classCount);
		final Node<?> b = new Data().setShape(classCount);
		final Node<?> y = $($(x, a), "+", b);
		final Node<?> cost = newCrossEntropyClassificationLoss(y, minibatchData.getLabels());
		
		initialize(random::nextGaussian, a, b);
		
		final GradientDescent gd = new GradientDescent(cost).setProcessor(this.getProcessor()).setIterations(1);
		gd.getParameters().add(a);
		gd.getParameters().add(b);
		final MinibatchMinimizer minibatchMinimizer = new MinibatchMinimizer(gd, trainingData, minibatchData).setEpochs(100);
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy(), trainingResult.getCounts());
			debugPrint(testData.getItemCount(), testResult.computeMacroF1(), testResult.computeAccuracy(), trainingResult.getCounts());
		}
		
		minibatchMinimizer.run();
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy(), trainingResult.getCounts());
			debugPrint(testData.getItemCount(), testResult.computeMacroF1(), testResult.computeAccuracy(), trainingResult.getCounts());
			
			assertTrue(0.98 <= testResult.computeAccuracy());
		}
	}
	
	public abstract NodeProcessor getProcessor();
	
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
	
	public static final void printTimers(final Map<Object, TicToc> timers) {
		System.out.println(debug(DEBUG_STACK_OFFSET + 1, timers.entrySet().stream()
				.map(e -> e.getKey() + ":" + e.getValue().getTotalTime()).collect(Collectors.toList())));
	}
	
}
