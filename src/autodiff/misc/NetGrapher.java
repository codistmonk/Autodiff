package autodiff.misc;

import static autodiff.learning.LearningTools.*;
import static autodiff.nodes.NodesTools.$;

import autodiff.io.Iris;
import autodiff.io.LabeledData;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.ui.JGraphXTools;

import java.util.Random;

import multij.swing.SwingTools;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-22)
 */
public final class NetGrapher {
	
	private NetGrapher() {
		throw new IllegalInstantiationException();
	}
	
	/**
	 * @param commandLineArguments
	 * <br>Unused
	 */
	public static final void main(final String... commandLineArguments) {
		final Random random = new Random(2L);
		final LabeledData allData = Iris.getIrisData();
		final Float[] classIds = packLabels(allData.getLabels());
		
		allData.shuffle(random);
		
		final LabeledData[] split = allData.split(2.0 / 3.0);
		final LabeledData trainingData = split[0];
//		final LabeledData testData = split[1];
		final int inputLength = trainingData.getInputLength();
		final int classCount = classIds.length;
		
		final Node<?> x = trainingData.getInputs();
		final Node<?> a = new Data().setShape(inputLength, classCount);
		final Node<?> b = new Data().setShape(classCount);
		final Node<?> y = $($(x, a), "+", b);
		final Node<?> cost = newCrossEntropyClassificationLoss(y, trainingData.getLabels());
		
		SwingTools.show(JGraphXTools.newGraphComponent(cost, 800, 800), "NetGrapher.cost");
	}

}
