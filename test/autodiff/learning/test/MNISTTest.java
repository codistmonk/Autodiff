package autodiff.learning.test;

import static autodiff.learning.LearningTools.*;
import static autodiff.nodes.NodesTools.$;
import static multij.tools.Tools.debugPrint;
import autodiff.computing.NodeProcessor;
import autodiff.io.LabeledData;
import autodiff.io.MNIST;
import autodiff.learning.ConfusionMatrix;
import autodiff.learning.GradientDescent;
import autodiff.learning.MinibatchMinimizer;
import autodiff.learning.Minimizer.Listener;
import autodiff.nodes.Data;
import autodiff.nodes.Node;

import java.util.Map;
import java.util.Random;

import multij.tools.Tools;

import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;

/**
 * @author codistmonk (creation 2016-08-08)
 */
public abstract class MNISTTest {
	
	protected MNISTTest() {
		// NOP
	}
	
	@Test
	@Ignore
	public final void test1() {
		final Random random = new Random(2L);
		final LabeledData trainingData = MNIST.getMNISTTrainingData();
		final LabeledData testData = MNIST.getMNISTTestData();
		final Map<Float, Integer> classIds = toIndexMap(trainingData.getLabels());
		
		packLabels(trainingData.getLabels(), classIds);
		packLabels(testData.getLabels(), classIds);
		
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.size();
		final int minibatchSize = 40;
		final LabeledData minibatchData = new LabeledData(minibatchSize, inputLength);
		
		final Node<?> x = minibatchData.getInputs();
		final Node<?> a = new Data().setShape(inputLength, classCount);
		final Node<?> b = new Data().setShape(classCount);
		final Node<?> y = $($(x, a), "+", b);
		final Node<?> cost = newCrossEntropyClassificationLoss(y, minibatchData.getLabels());
		
		initialize(random::nextGaussian, 1E-3, a, b);
		
		final GradientDescent gd = new GradientDescent(cost).setLearningRate(1E-5F).setIterations(1);
		gd.getParameters().add(a);
		gd.getParameters().add(b);
		final MinibatchMinimizer minibatchMinimizer = new MinibatchMinimizer(
				gd, trainingData, minibatchData).setEpochs(2);
		
		minibatchMinimizer.getListeners().add(new Listener() {
			
			@Override
			public final void beforeUpdateCost(final float previousBestCost) {
				Tools.debugPrint("epoch:", minibatchMinimizer.getCurrentEpoch());
			}
			
			@Override
			public final void afterUpdateCost(final float cost, final float newBestCost) {
				Tools.debugPrint("cost:", cost, "newBestCost:", newBestCost);
			}
			
			private static final long serialVersionUID = -268955802659280286L;
			
		});
		
		if (true) {
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy(), trainingResult.getCounts());
			debugPrint(testData.getItemCount(), testResult.computeMacroF1(), testResult.computeAccuracy(), testResult.getCounts());
		}
		
		minibatchMinimizer.run();
		
		{
			final ConfusionMatrix<Integer> trainingResult = evaluate(y, trainingData, minibatchData, this.getProcessor());
			final ConfusionMatrix<Integer> testResult = evaluate(y, testData, minibatchData, this.getProcessor());
			
			debugPrint(trainingData.getItemCount(), trainingResult.computeMacroF1(), trainingResult.computeAccuracy(), trainingResult.getCounts());
			debugPrint(testData.getItemCount(), testResult.computeMacroF1(), testResult.computeAccuracy(), trainingResult.getCounts());
		}
		
		GradientDescentTest.printTimers(this.getProcessor().getTimers());
		
		Assert.fail("TODO");
	}
	
	public abstract NodeProcessor getProcessor();
	
}
