package autodiff.ui;

import static multij.swing.SwingTools.scrollable;
import autodiff.nodes.BinaryNode;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.UnaryNode;
import autodiff.nodes.Zipping;

import com.mxgraph.model.mxGeometry;
import com.mxgraph.model.mxIGraphModel;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import javax.swing.AbstractAction;
import javax.swing.JDialog;
import javax.swing.JPopupMenu;
import javax.swing.JTable;
import javax.swing.SwingUtilities;
import javax.swing.WindowConstants;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableModel;

import multij.swing.MouseHandler;
import multij.swing.SwingTools;
import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;

/**
 * @author codistmonk (creation 2016-07-22)
 */
public final class JGraphXTools {
	
	private JGraphXTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final mxGraph newGraph(final Node<?> node, final int componentWidth,
			final int componentHeight, final int cellWidth, final int cellHeight) {
		return newGraph(node, componentWidth, componentHeight, cellWidth, cellHeight, new HashMap<>());
	}
	
	public static final mxGraph newGraph(final Node<?> node, final int componentWidth,
			final int componentHeight, final int cellWidth, final int cellHeight,
			final Map<Node<?>, Object> vertices) {
		final mxGraph graph = new mxGraph();
		final mxIGraphModel graphModel = graph.getModel();
		final Object parent = graph.getDefaultParent();
		final Map<Node<?>, Integer> depths = new LinkedHashMap<>();
		
		node.accept(new NodeVisitor<Object>() {
			
			private final Collection<Pair<Object, Object>> edges = new HashSet<>();
			
			private int depth = -1;
			
			@Override
			public final Object visit(final Node<?> node) {
				final Object result = this.begin(node);
				final int n = node.getArguments().size();
				
				for (int i = 0; i < n; ++i) {
					this.connect(node.getArguments().get(i), "" + i, result);
				}
				
				return this.end(result);
			}
			
			@Override
			public final Object visit(final UnaryNode<?> node) {
				final Object result = this.begin(node);
				
				this.connect(node.getArgument(), "argument", result);
				
				return this.end(result);
			}
			
			@Override
			public final Object visit(final BinaryNode<?> node) {
				final Object result = this.begin(node);
				
				this.connect(node.getLeft(), "left", result);
				this.connect(node.getRight(), "right", result);
				
				return this.end(result);
			}
			
			@Override
			public final Object visit(final MatrixMultiplication node) {
				final Object result = this.visit((BinaryNode<?>) node);
				
				graphModel.setValue(result, defaultNodeText(node) + "\n"
				+ (node.isTransposeLeft() ? "T" : "N") + (node.isTransposeRight() ? "T" : "N"));
				
				return result;
			}
			
			@Override
			public final Object visit(final Zipping node) {
				final Object result = this.visit((BinaryNode<?>) node);
				
				graphModel.setValue(result, defaultNodeText(node) + "\n" + node.getFunctionName());
				
				return result;
			}
			
			@Override
			public final Object visit(final Mapping node) {
				final Object result = this.visit((UnaryNode<?>) node);
				
				graphModel.setValue(result, defaultNodeText(node) + "\n" + node.getFunctionName());
				
				return result;
			}
			
			private final void connect(final Node<?> argument, final String text, final Object targetVertex) {
				final Object argumentVertex = argument.accept(this);
				
				if (this.edges.add(new Pair<>(argumentVertex, targetVertex))) {
					graph.insertEdge(parent, null, text, argumentVertex, targetVertex);
				}
			}
			
			private final Object begin(final Node<?> node) {
				++this.depth;
				
				depths.put(node, Math.max(this.depth, depths.getOrDefault(node, 0)));
				
				return vertices.computeIfAbsent(node,
						n -> graph.insertVertex(parent, null, defaultNodeText(n),
								componentWidth / 2, componentHeight / 2, cellWidth, cellHeight));
			}
			
			private final Object end(final Object vertex) {
				--this.depth;
				
				return vertex;
			}
			
			private static final long serialVersionUID = 8210701219373622680L;
			
		});
		
		final Map<Integer, List<Node<?>>> nodes = new TreeMap<>();
		
		depths.forEach((k, v) -> nodes.computeIfAbsent(v, __ -> new ArrayList<>()).add(k));
		
		final int d = nodes.size();
		
		nodes.forEach((k, v) -> {
			final int m = v.size();
			
			for (int i = 0; i < m; ++i) {
				final Node<?> n = v.get(i);
				final mxGeometry cellGeometry = graph.getCellGeometry(vertices.get(n));
				
				cellGeometry.setX((componentWidth / m / 2) + i * componentWidth / m - cellWidth / 2);
				cellGeometry.setY(componentHeight - (componentHeight / d / 2) - k * componentHeight / d - cellHeight / 2);
			}
		});
		
		graph.refresh();
		
		return graph;
	}
	
	public static final <K, V> Map<V, K> reverse(final Map<K, V> map, final Map<V, K> result) {
		map.forEach((k, v) -> result.put(v, k));
		
		return result;
	}
	
	public static final mxGraphComponent newGraphComponent(final Node<?> node, final int componentWidth, final int componentHeight) {
		final int cellWidth = 150;
		final int cellHeight = 50;
		final Map<Node<?>, Object> vertices = new HashMap<>();
		final mxGraph graph = newGraph(node, componentWidth, componentHeight,
				cellWidth, cellHeight, vertices);
		final Map<Object, Node<?>> nodes = reverse(vertices, new HashMap<>());
		final mxGraphComponent result = new mxGraphComponent(graph);
		
		new MouseHandler() {
			
			private final JPopupMenu nodeMenu = new JPopupMenu();
			
			private Object currentCell;
			
			{
				this.nodeMenu.add(new AbstractAction("Show values...") {
					
					@Override
					public final void actionPerformed(final ActionEvent event) {
						showNodeValues(nodes);
					}
					
					private static final long serialVersionUID = -6081193936361106487L;
					
				});
			}
			
			@Override
			public final void mouseClicked(final MouseEvent event) {
				this.maybeShowPopup(event);
			}
			
			@Override
			public final void mousePressed(final MouseEvent event) {
				this.maybeShowPopup(event);
			}
			
			@Override
			public final void mouseReleased(final MouseEvent event) {
				this.maybeShowPopup(event);
			}
			
			final void showNodeValues(final Map<Object, Node<?>> nodes) {
				final Node<?> node = nodes.get(this.currentCell);
				
				final JDialog view = new JDialog(SwingUtilities.getWindowAncestor(result), "Values");
				
				view.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
				view.getContentPane().add(scrollable(new JTable(newTableModel(node))));
				
				SwingTools.packAndCenter(view).setVisible(true);
			}
			
			private final void maybeShowPopup(final MouseEvent event) {
				this.currentCell = result.getCellAt(event.getX(), event.getY());
				
				if (event.isPopupTrigger()) {
					this.nodeMenu.show(event.getComponent(), event.getX(), event.getY());
				}
			}

			private static final long serialVersionUID = 866265828188334632L;
			
		}.addTo(result.getGraphControl());
		
		result.setPreferredSize(new Dimension(componentWidth, componentHeight));
		
		return result;
	}
	
	public static final String defaultNodeText(final Node<?> node) {
		return node.getClass().getSimpleName() + Arrays.toString(node.getShape());
	}
	
	public static final TableModel newTableModel(final Node<?> node) {
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
	
}
