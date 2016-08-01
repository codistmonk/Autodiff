package autodiff.ui;

import static javax.swing.SwingUtilities.getWindowAncestor;

import autodiff.nodes.BinaryNode;
import autodiff.nodes.Mapping;
import autodiff.nodes.MatrixMultiplication;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.ShapeNode;
import autodiff.nodes.Zipping;

import com.mxgraph.model.mxGeometry;
import com.mxgraph.model.mxIGraphModel;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import java.awt.Component;
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
import java.util.function.Supplier;

import javax.swing.AbstractAction;
import javax.swing.JDialog;
import javax.swing.JPopupMenu;
import javax.swing.JTabbedPane;
import javax.swing.WindowConstants;

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
	
	public static final int DEFAULT_CELL_WIDTH = 160;
	
	public static final int DEFAULT_CELL_HEIGHT = 50;
	
	public static final mxGraph newGraph(final Node<?> node, final int cellWidth, final int cellHeight) {
		return newGraph(Arrays.asList(node), cellWidth, cellHeight, new HashMap<>(), new LinkedHashMap<>());
	}
	
	public static final mxGraph newGraph(final Iterable<Node<?>> nodes, final int cellWidth, final int cellHeight,
			final Map<Node<?>, Object> vertices, final Map<Node<?>, Integer> depths) {
		final mxGraph graph = new mxGraph();
		final mxIGraphModel graphModel = graph.getModel();
		final Object parent = graph.getDefaultParent();
		final NodeVisitor<Object> visitor = new NodeVisitor<Object>() {
			
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
				final Object result = this.begin(node);
				
				this.connect(node.getArgument(), "argument", result);
				
				graphModel.setValue(result, defaultNodeText(node) + "\n" + node.getFunctionName());
				
				return this.end(result);
			}
			
			@Override
			public final Object visit(final ShapeNode node) {
				final Object result = this.begin(node);
				
				this.connect(node.getSource(), "source", result);
				
				graphModel.setValue(result, defaultNodeText(node));
				
				return this.end(result);
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
								0, 0, cellWidth, cellHeight));
			}
			
			private final Object end(final Object vertex) {
				--this.depth;
				
				return vertex;
			}
			
			private static final long serialVersionUID = 8210701219373622680L;
			
		};
		
		for (final Node<?> node : nodes) {
			node.accept(visitor);
		}
		
		return graph;
	}
	
	public static final <K, V> Map<V, K> reverse(final Map<K, V> map, final Map<V, K> result) {
		map.forEach((k, v) -> result.put(v, k));
		
		return result;
	}
	
	public static final <K, V, C extends Collection<K>> Map<V, C> reverseMulti(final Map<K, V> map,
			final Map<V, C> result, final Supplier<C> collectionSupplier) {
		map.forEach((k, v) -> result.computeIfAbsent(v, __ -> collectionSupplier.get()).add(k));
		
		return result;
	}
	
	public static final mxGraphComponent newGraphComponent(final Node<?> node) {
		return newGraphComponent(Arrays.asList(node), DEFAULT_CELL_WIDTH, DEFAULT_CELL_HEIGHT);
	}
	
	public static final mxGraphComponent newGraphComponent(final Iterable<Node<?>> nodes, final int cellWidth, final int cellHeight) {
		final Map<Node<?>, Object> vertices = new HashMap<>();
		final Map<Node<?>, Integer> depths = new LinkedHashMap<>();
		final mxGraph graph = newGraph(nodes, cellWidth, cellHeight, vertices, depths);
		final Map<Object, Node<?>> nodesByCell = reverse(vertices, new HashMap<>());
		final Map<Integer, List<Node<?>>> nodesByDepth = reverseMulti(depths, new TreeMap<>(), ArrayList::new);
		final int d = nodesByDepth.size();
		final int d1 = nodesByDepth.values().stream().mapToInt(Collection::size).max().getAsInt();
		final int componentWidth = (2 * d1 + 1) * cellWidth / 2;
		final int componentHeight = (2 * d + 1) * cellHeight;
		
		nodesByDepth.forEach((k, v) -> {
			final int m = v.size();
			
			for (int i = 0; i < m; ++i) {
				final Node<?> n = v.get(i);
				final mxGeometry cellGeometry = graph.getCellGeometry(vertices.get(n));
				
				cellGeometry.setX((componentWidth / m / 2) + i * componentWidth / m - cellWidth / 2);
				cellGeometry.setY(componentHeight - (componentHeight / d / 2) - k * componentHeight / d - cellHeight / 2);
			}
		});
		
		graph.refresh();
		
		final mxGraphComponent result = new mxGraphComponent(graph);
		
		new MouseHandler() {
			
			private final JPopupMenu nodeMenu = new JPopupMenu();
			
			private Object currentCell;
			
			{
				this.nodeMenu.add(new AbstractAction("Values...") {
					
					@Override
					public final void actionPerformed(final ActionEvent event) {
						showValues(nodesByCell);
					}
					
					private static final long serialVersionUID = -6081193936361106487L;
					
				});
				this.nodeMenu.add(new AbstractAction("Backward diff nodes...") {
					
					@Override
					public final void actionPerformed(final ActionEvent event) {
						showBackwardDiffNodes(nodesByCell);
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
			
			final void showBackwardDiffNodes(final Map<Object, Node<?>> nodesByCell) {
				final Node<?> node = nodesByCell.get(this.currentCell);
				final List<Node<?>> backwardDiffNodes = node.getBackwardDiffNodes();
				
				if (backwardDiffNodes != null && !backwardDiffNodes.isEmpty()) {
					final mxGraphComponent component = JGraphXTools.newGraphComponent(backwardDiffNodes,
							DEFAULT_CELL_WIDTH, DEFAULT_CELL_HEIGHT);
					
					this.show(component, "Backward diff nodes");
				}
			}
			
			final void showValues(final Map<Object, Node<?>> nodesByCell) {
				final Node<?> node = nodesByCell.get(this.currentCell);
				final JTabbedPane component = autodiff.ui.SwingTools.newNodeValuesView(node);
				
				this.show(component, "Values");
			}
			
			private final void show(final Component component, final String title) {
				final JDialog view = new JDialog(getWindowAncestor(result), title);
				
				view.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
				view.getContentPane().add(component);
				
				SwingTools.packAndCenter(view).setVisible(true);
			}
			
			private final void maybeShowPopup(final MouseEvent event) {
				this.currentCell = result.getCellAt(event.getX(), event.getY());
				
				if (this.currentCell != null && event.isPopupTrigger()) {
					this.nodeMenu.show(event.getComponent(), event.getX(), event.getY());
				}
			}
			
			private static final long serialVersionUID = 866265828188334632L;
			
		}.addTo(result.getGraphControl());
		
		result.setPreferredSize(new Dimension(componentWidth, componentHeight));
		
		return result;
	}
	
	public static final String defaultNodeText(final Node<?> node) {
		return node.getId() + ":" + node.getClass().getSimpleName() + Arrays.toString(node.getShape());
	}
	
}
