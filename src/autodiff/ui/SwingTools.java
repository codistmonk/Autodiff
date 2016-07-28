package autodiff.ui;

import static java.lang.Math.max;
import static multij.swing.SwingTools.scrollable;

import autodiff.nodes.Node;
import autodiff.nodes.NodesTools;

import java.awt.Point;
import java.awt.Rectangle;
import java.awt.event.AdjustmentEvent;
import java.awt.event.AdjustmentListener;

import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.ScrollPaneConstants;
import javax.swing.SwingUtilities;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableModel;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-28)
 */
public final class SwingTools {
	
	private SwingTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final JTabbedPane newNodeValuesView(final Node<?> node) {
		final JTabbedPane result = new JTabbedPane();
		
		result.add("List", scrollable(new JTable(newListViewTableModel(node))));
		
		final JTable arrayView = new JTable();
		final int n = node.getShape().length;
		
		arrayView.setModel(freeze(newArrayViewTableModel(node), (n + 1) / 2 + 2, n / 2 + 2, arrayView));
		arrayView.setTableHeader(null);
		arrayView.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
		
		final JScrollPane arrayScroll = new JScrollPane(arrayView,
				ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		
		arrayScroll.getHorizontalScrollBar().addAdjustmentListener(new AdjustmentListener() {
			
			@Override
			public final void adjustmentValueChanged(final AdjustmentEvent event) {
				arrayView.repaint();
			}
			
		});
		
		arrayScroll.getVerticalScrollBar().addAdjustmentListener(new AdjustmentListener() {
			
			@Override
			public final void adjustmentValueChanged(final AdjustmentEvent event) {
				arrayView.repaint();
			}
			
		});
		
		result.add("Array", arrayScroll);
		
		return result;
	}
	
	public static final TableModel newListViewTableModel(final Node<?> node) {
		final String[] COLUMN_NAMES = { "Index", "Value" };
		
		return new AbstractTableModel() {
			
			@Override
			public final String getColumnName(final int column) {
				return COLUMN_NAMES[column];
			}
			
			@Override
			public final Object getValueAt(final int rowIndex, final int columnIndex) {
				return columnIndex == 0 ? "" + rowIndex : node.get(rowIndex);
			}
			
			@Override
			public final int getRowCount() {
				return node.getLength();
			}
			
			@Override
			public final int getColumnCount() {
				return 2;
			}
			
			private static final long serialVersionUID = 4478430067103819240L;
			
		};
	}
	
	public static final TableModel freeze(final TableModel source, final int row, final int column, final JTable table) {
		return new AbstractTableModel() {
			
			@Override
			public final Object getValueAt(final int rowIndex, final int columnIndex) {
				final Rectangle cellRect = table.getCellRect(rowIndex, columnIndex, false);
				final Point xy = SwingUtilities.convertPoint(table, new Point(cellRect.x, cellRect.y), table.getParent());
				final int viewRow = max(0, xy.y / table.getRowHeight());
				final int viewColumn = max(0, xy.x / table.getColumnModel().getColumn(0).getWidth());
				final int sourceRow = viewRow < row ? viewRow : rowIndex;
				final int sourceColumn = viewColumn < column ? viewColumn : columnIndex;
				
				return source.getValueAt(sourceRow, sourceColumn);
			}
			
			@Override
			public int getRowCount() {
				return source.getRowCount();
			}
			
			@Override
			public int getColumnCount() {
				return source.getColumnCount();
			}
			
			private static final long serialVersionUID = 306064580259235744L;
			
		};
	}
	
	public static final TableModel newArrayViewTableModel(final Node<?> node) {
		final int[] shape = node.getShape();
		
		return new AbstractTableModel() {
			
			private int rowCount = 1;
			
			private int columnCount = 1;
			
			private final int[] verticalStrides = new int[(shape.length + 1) / 2];
			
			private final int[] horizontalStrides = new int[shape.length / 2];
			
			private final int[] indices = new int[shape.length];
			
			{
				for (int i = this.verticalStrides.length - 1; 0 <= i; --i) {
					if (i == this.verticalStrides.length - 1) {
						this.verticalStrides[i] = shape[2 * i] + 1;
					} else {
						this.verticalStrides[i] = shape[2 * i] * this.verticalStrides[i + 1] + 1;
					}
				}
				
				for (int i = this.horizontalStrides.length - 1; 0 <= i; --i) {
					if (i == this.horizontalStrides.length - 1) {
						this.horizontalStrides[i] = shape[2 * i + 1] + 1;
					} else {
						this.horizontalStrides[i] = shape[2 * i + 1] * this.horizontalStrides[i + 1] + 1;
					}
				}
				
				if (0 < this.verticalStrides.length) {
					this.rowCount = this.verticalStrides[0];
				}
				
				if (0 < this.horizontalStrides.length) {
					this.columnCount = this.horizontalStrides[0];
				}
			}
			
			@Override
			public final Object getValueAt(final int rowIndex, final int columnIndex) {
				
				if (rowIndex < this.horizontalStrides.length) {
					if (columnIndex == this.verticalStrides.length) {
						return "(" + (rowIndex * 2 + 1) + ")";
					} else if (this.verticalStrides.length < columnIndex && columnIndex < this.verticalStrides.length + this.horizontalStrides[0]) {
						final int index = this.indexAt(0, columnIndex - 1 - this.verticalStrides.length);
						
						return index < 0 ? "" : this.indices[rowIndex * 2 + 1];
					}
					
					return "";
				}
				
				if (columnIndex < this.verticalStrides.length) {
					if (rowIndex == this.horizontalStrides.length) {
						return "(" + (columnIndex * 2) + ")";
					} else if (this.horizontalStrides.length < rowIndex && rowIndex < this.horizontalStrides.length + this.verticalStrides[0]) {
						final int index = this.indexAt(rowIndex - 1 - this.horizontalStrides.length, 0);
						
						return index < 0 ? "" : this.indices[columnIndex * 2];
					}
					
					return "";
				}
				
				if (rowIndex == this.horizontalStrides.length || columnIndex == this.verticalStrides.length) {
					return "";
				}
				
				final int index = this.indexAt(rowIndex - 1 - this.horizontalStrides.length, columnIndex - 1 - this.verticalStrides.length);
				
				return index < 0 ? "" : node.get(index);
			}
			
			private final int indexAt(final int rowIndex, final int columnIndex) {
				{
					int tmp = columnIndex;
					
					for (int i = 1; i < this.indices.length; i += 2) {
						final int s = i / 2 + 1 < this.horizontalStrides.length ? this.horizontalStrides[i / 2 + 1] : 1;
						this.indices[i] = tmp / s;
						tmp %= s;
						
						if (shape[i] <= this.indices[i]) {
							return -1;
						}
					}
				}
				
				{
					int tmp = rowIndex;
					
					for (int i = 0; i < this.indices.length; i += 2) {
						final int s = i / 2 + 1 < this.verticalStrides.length ? this.verticalStrides[i / 2 + 1] : 1;
						this.indices[i] = tmp / s;
						tmp %= s;
						
						if (shape[i] <= this.indices[i]) {
							return -1;
						}
					}
				}
				
				return NodesTools.indexFromCartesian(shape, this.indices);
			}
			
			@Override
			public final int getRowCount() {
				return this.rowCount + 1 + this.horizontalStrides.length;
			}
			
			@Override
			public final int getColumnCount() {
				return this.columnCount + 1 + this.verticalStrides.length;
			}
			
			private static final long serialVersionUID = 4478430067103819240L;
			
		};
	}
	
}
