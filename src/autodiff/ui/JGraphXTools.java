package autodiff.ui;

import autodiff.nodes.BinaryNode;
import autodiff.nodes.Mapping;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.UnaryNode;
import autodiff.nodes.Zipping;

import com.mxgraph.model.mxGeometry;
import com.mxgraph.model.mxIGraphModel;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import java.awt.Dimension;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

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
		final mxGraph graph = new mxGraph();
		final mxIGraphModel graphModel = graph.getModel();
		final Object parent = graph.getDefaultParent();
		final Map<Node<?>, Object> vertices = new HashMap<>();
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
	
	public static final mxGraphComponent newGraphComponent(final Node<?> node, final int componentWidth, final int componentHeight) {
		final int cellWidth = 150;
		final int cellHeight = 50;
		final mxGraph graph = newGraph(node, componentWidth, componentHeight,
				cellWidth, cellHeight);
		final mxGraphComponent result = new mxGraphComponent(graph);
		
		result.setPreferredSize(new Dimension(componentWidth, componentHeight));
		
		return result;
	}
	
	public static final String defaultNodeText(final Node<?> node) {
		return node.getClass().getSimpleName() + Arrays.toString(node.getShape());
	}
	
}
