package autodiff.io;

import static multij.tools.Tools.ignore;

import java.io.InputStream;
import java.io.Serializable;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import multij.primitivelists.FloatList;

/**
 * @author codistmonk (creation 2016-03-08)
 */
public abstract interface CSVParser extends Serializable {
	
	public abstract void cell(String string);
	
	public abstract void endOfRow();
	
	public static <R extends CSVParser> R readCSV(final InputStream input, final R reader) {
		return readCSV(input, ",", reader);
	}
	
	public static <R extends CSVParser> R readCSV(final InputStream input, final String separator, final R reader) {
		try (final Scanner scanner = new Scanner(input)) {
			while (scanner.hasNext()) {
				try (final Scanner lineScanner = new Scanner(scanner.nextLine())) {
					lineScanner.useDelimiter(separator);
					
					while (lineScanner.hasNext()) {
						reader.cell(lineScanner.next());
					}
				}
				
				reader.endOfRow();
			}
		}
		
		return reader;
	}
	
	/**
	 * @author codistmonk (creation 2016-03-08)
	 */
	public static final class FloatData implements CSVParser {
		
		private final List<float[]> records;
		
		private final Map<Integer, CSVParser.BiMap<String, Integer>> categories;
		
		private final FloatList record;
		
		public FloatData() {
			this.records = new ArrayList<>();
			this.categories = new HashMap<>();
			this.record = new FloatList();
		}
		
		public final float[] getRecord(final int index) {
			return this.getRecords().get(index);
		}
		
		public final List<float[]> getRecords() {
			return this.records;
		}
		
		public final Map<Integer, CSVParser.BiMap<String, Integer>> getCategories() {
			return this.categories;
		}
		
		public final CSVParser.BiMap<String, Integer> getCategory(final int index) {
			return this.getCategories().get(index);
		}
		
		public final int getClassIndex(final int categoryIndex, final String className) {
			return this.getCategory(categoryIndex).get(className);
		}
		
		public final String getClassName(final int categoryIndex, final int classIndex) {
			return this.getCategory(categoryIndex).backwardGet(classIndex);
		}
		
		@Override
		public final void cell(final String string) {
			try {
				this.record.add(Float.parseFloat(string));
			} catch (final NumberFormatException exception) {
				ignore(exception);
				
				final CSVParser.BiMap<String, Integer> map = this.getCategories().computeIfAbsent(this.record.size(), k -> new CSVParser.BiMap<>());
				
				this.record.add(map.computeIfAbsent(string, k -> map.size()));
			}
		}
		
		@Override
		public final void endOfRow() {
			this.getRecords().add(this.record.toArray().clone());
			this.record.clear();
		}
		
		private static final long serialVersionUID = 6519389741606296293L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-03-08)
	 */
	public static final class BiMap<K, V> extends AbstractMap<K, V> implements Serializable {
		
		private final Map<K, V> forward = new HashMap<>();
		
		private final Map<V, K> backward = new HashMap<>();
		
		public final Map<K, V> getForward() {
			return this.forward;
		}
		
		public final Map<V, K> getBackward() {
			return this.backward;
		}
		
		public final K backwardGet(final V value) {
			return this.getBackward().get(value);
		}
		
		@Override
		public Set<Map.Entry<K, V>> entrySet() {
			return this.getForward().entrySet();
		}
		
		@Override
		public final V put(final K key, final V value) {
			final V result = this.getForward().put(key, value);
			
			this.getBackward().put(value, key);
			
			return result;
		}
		
		@Override
		public final V remove(final Object key) {
			final V result = this.getForward().remove(key);
			
			this.getBackward().remove(result);
			
			return result;
		}
		
		@Override
		public final void putAll(final Map<? extends K, ? extends V> m) {
			m.forEach((k, v) -> {
				this.put(k, v);
				this.getBackward().put(v, k);
			});
		}
		
		private static final long serialVersionUID = 476685479486955703L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-03-08)
	 */
	public static final class StringData implements CSVParser {
		
		private final List<List<String>> records;
		
		private List<String> record;
		
		public StringData() {
			this(new ArrayList<>());
		}
		
		public StringData(final List<List<String>> records) {
			this.records = records;
			this.record = new ArrayList<>();
		}
		
		public final List<List<String>> getRecords() {
			return this.records;
		}
		
		@Override
		public final void cell(final String string) {
			this.record.add(string);
		}
		
		@Override
		public final void endOfRow() {
			this.getRecords().add(this.record);
			this.record = new ArrayList<>();
		}
		
		private static final long serialVersionUID = 4904327823280338722L;
		
		public static final List<List<String>> readCSV(final InputStream input, final String separator) {
			return CSVParser.readCSV(input, separator, new StringData()).getRecords();
		}
		
	}
	
}