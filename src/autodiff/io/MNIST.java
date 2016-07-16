package autodiff.io;

import static multij.tools.Tools.*;

import autodiff.nodes.Data;
import autodiff.nodes.Node;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-15)
 */
public final class MNIST {
	
	private MNIST() {
		throw new IllegalInstantiationException();
	}
	
	public static final LabeledData getMNISTTestData() {
		final String testImagesFilePath = "lib/data/mnist/t10k-images-idx3-ubyte.gz";
		final String testLabelsFilePath = "lib/data/mnist/t10k-labels-idx1-ubyte.gz";
		
		return readData("mnist_test.jo", testImagesFilePath, testLabelsFilePath);
	}
	
	public static final LabeledData getMNISTTrainingData() {
		final String trainingImagesFilePath = "lib/data/mnist/train-images-idx3-ubyte.gz";
		final String trainingLabelsFilePath = "lib/data/mnist/train-labels-idx1-ubyte.gz";
		
		return readData("mnist_training.jo", trainingImagesFilePath, trainingLabelsFilePath);
	}
	
	public static final LabeledData readData(final String cacheKey, final String inputsFilePath, final String labelsFilePath) {
		try {
			return readObject(cacheKey);
		} catch (final Exception exception) {
			debugError(exception);
		}
		
		final List<float[]> records = new ArrayList<>();
		
		IDX.readUByteGZFAsFloats(inputsFilePath, data -> records.add(data.clone()));
		
		final int d = records.get(0).length;
		final int n = records.size();
		final Node<?> inputs = new Data().setShape(n, d);
		final Node<?> labels = new Data().setShape(n);
		
		for (int i = 0; i < n; ++i) {
			for (int j = 0; j < d; ++j) {
				inputs.set(i * d + j, records.get(i)[j]);
			}
		}
		
		IDX.readUByteGZFAsFloats(labelsFilePath, new Consumer<float[]>() {
			
			private int i = -1;
			
			@Override
			public final void accept(final float[] t) {
				labels.set(++this.i, t[0]);
			}
			
		});
		
		final LabeledData result = new LabeledData(inputs, labels);
		
		writeObject(result, cacheKey);
		
		return result;
	}
	
}
