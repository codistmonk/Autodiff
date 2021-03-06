package autodiff.misc;

import static autodiff.learning.LearningTools.*;
import static autodiff.nodes.NodesTools.$;
import autodiff.computing.DefaultProcessor;
import autodiff.computing.NodeProcessor;
import autodiff.io.Iris;
import autodiff.io.LabeledData;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.nodes.NodesTools;
import autodiff.ui.JGraphXTools;

import java.util.Map;
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
		final String net = "cost";
		final NodeProcessor processor = DefaultProcessor.INSTANCE;
		
		if ("cost".equals(net)) {
			final Random random = new Random(2L);
			final LabeledData allData = Iris.getIrisData();
			final Map<Float, Integer> classIds = toIndexMap(allData.getLabels());
			
			packLabels(allData.getLabels(), classIds);
			
			allData.shuffle(random);
			
			final LabeledData[] split = allData.split(2.0 / 3.0);
			final LabeledData trainingData = split[0];
//			final LabeledData testData = split[1];
			final int inputLength = trainingData.getInputLength();
			final int classCount = classIds.size();
			
			final Node<?> x = trainingData.getInputs();
			final Node<?> a = new Data().setShape(inputLength, classCount);
			final Node<?> b = new Data().setShape(classCount);
			final Node<?> y = $($(x, a), "+", b);
			final Node<?> cost = newCrossEntropyClassificationLoss(y, trainingData.getLabels());
			
			processor.fullForward(cost);
			
			a.setupDiffs(true);
			b.setupDiffs(true);
			
			processor.fullBackwardDiff(cost);
			
			SwingTools.show(JGraphXTools.newGraphComponent(cost), "NetGrapher." + net);
		} else if ("sorting".equals(net)) {
			final Node<?> node = NodesTools.sortIndices($(5, 3, 1, 4, 2).shaped(1, 5));
			
			processor.fullForward(node);
			
			SwingTools.show(JGraphXTools.newGraphComponent(node), "NetGrapher." + net);
		} else {
			final Node<?> md = new Data().setShape(2, 3, 4, 5, 6);
			
			for (int i = 0; i < md.getLength(); ++i) {
				md.set(i, i);
			}
			
			SwingTools.show(JGraphXTools.newGraphComponent(md), "NetGrapher." + net);
		}
	}

}
