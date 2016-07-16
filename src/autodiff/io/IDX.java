package autodiff.io;

import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.zip.GZIPInputStream;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-03-09)
 */
public final class IDX {
	
	private IDX() {
		throw new IllegalInstantiationException();
	}
	
	public static final int MAGIC_IDX1 = 0x00000801;
	
	public static final int MAGIC_IDX3 = 0x00000803;
	
	public static final List<Integer> readLabels(final String trainingLabelsFilePath) {
		final List<Integer> result = new ArrayList<>();
		
		readUByteGZ(trainingLabelsFilePath, label -> result.add((int) label[0]));
		
		return result;
	}
	
	public static final List<double[]> readInputs(final String trainingImagesFilePath) {
		final List<double[]> result = new ArrayList<>();
		
		readUByteGZ(trainingImagesFilePath, input -> result.add(input.clone()));
		
		return result;
	}
	
	public static final void readUByteGZ(final String filePath, final Consumer<double[]> itemProcessor) {
		try (final DataInputStream input = new DataInputStream(new GZIPInputStream(new FileInputStream(filePath)))) {
			final int magic = input.readInt();
			final int items = input.readInt();
			
			Tools.debugPrint("magic:", Integer.toHexString(magic), "items:", items);
			
			switch (magic) {
			case MAGIC_IDX1:
			{
				final double[] buffer = { 0.0 };
				
				for (int i = 0; i < items; ++i) {
					buffer[0] = read1(input);
					
					itemProcessor.accept(buffer);
				}
				
				break;
			}
			case MAGIC_IDX3:
			{
				final int rows = input.readInt();
				final int columns = input.readInt();
				final int m = rows * columns;
				final double[] buffer = new double[m];
				
				for (int i = 0; i < items; ++i) {
					for (int j = 0; j < m; ++j) {
						buffer[j] = read1(input);
					}
					
					itemProcessor.accept(buffer);
				}
				
				break;
			}
			default:
				throw new IllegalArgumentException();
			}
		} catch (final IOException exception) {
			throw new UncheckedIOException(exception);
		}
	}
	
	public static final void readUByteGZFAsFloats(final String filePath, final Consumer<float[]> itemProcessor) {
		try (final DataInputStream input = new DataInputStream(new GZIPInputStream(new FileInputStream(filePath)))) {
			final int magic = input.readInt();
			final int items = input.readInt();
			
			Tools.debugPrint("magic:", Integer.toHexString(magic), "items:", items);
			
			switch (magic) {
			case MAGIC_IDX1:
			{
				final float[] buffer = { 0F };
				
				for (int i = 0; i < items; ++i) {
					buffer[0] = read1(input);
					
					itemProcessor.accept(buffer);
				}
				
				break;
			}
			case MAGIC_IDX3:
			{
				final int rows = input.readInt();
				final int columns = input.readInt();
				final int m = rows * columns;
				final float[] buffer = new float[m];
				
				for (int i = 0; i < items; ++i) {
					for (int j = 0; j < m; ++j) {
						buffer[j] = read1(input);
					}
					
					itemProcessor.accept(buffer);
				}
				
				break;
			}
			default:
				throw new IllegalArgumentException();
			}
		} catch (final IOException exception) {
			throw new UncheckedIOException(exception);
		}
	}
	
	public static final int read1(final DataInputStream input) throws IOException {
		final int datum = input.read();
		
		if (datum < 0) {
			throw new UncheckedIOException(new IOException("Unexpected end of input"));
		}
		
		return datum;
	}
	
}
