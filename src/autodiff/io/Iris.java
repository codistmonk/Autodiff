package autodiff.io;

import static multij.tools.Tools.debugError;
import static multij.tools.Tools.readObject;
import static multij.tools.Tools.writeObject;

import java.util.List;

import autodiff.io.CSVParser.FloatData;
import autodiff.nodes.Data;
import autodiff.nodes.Node;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-07-16)
 */
public final class Iris {
	
	private Iris() {
		throw new IllegalInstantiationException();
	}
	
	public static final LabeledData getIrisData() {
		return readData("iris.jo", "lib/data/iris/iris.data");
	}
	
	public static final LabeledData readData(final String cacheKey, final String csvFilePath) {
		try {
			return readObject(cacheKey);
		} catch (final Exception exception) {
			debugError(exception);
		}
		
		final FloatData records = CSVParser.readCSV(Tools.getResourceAsStream(csvFilePath), new CSVParser.FloatData());
		final LabeledData result = toLabeledData(records.getRecords());
		
		writeObject(result, cacheKey);
		
		return result;
	}
	
	public static final LabeledData toLabeledData(final List<float[]> records) {
		return toLabeledData(records, records.get(0).length - 1);
	}
	
	public static final LabeledData toLabeledData(final List<float[]> records, final int classIndex) {
		final int itemCount = records.size();
		final int inputLength = records.get(0).length - 1;
		final Node<?> inputs = new Data().setShape(itemCount, inputLength);
		final Node<?> labels = new Data().setShape(itemCount);
		
		for (int i = 0, k = 0; i < itemCount; ++i) {
			final float[] record = records.get(i);
			
			for (int j = 0; j <= inputLength; ++j) {
				if (j != classIndex) {
					inputs.set(k, record[j]);
					++k;
				}
			}
			
			labels.set(i, record[classIndex]);
		}
		
		return new LabeledData(inputs, labels);
	}
	
}
