package autodiff.ui;

import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Zipping;

import com.mxgraph.model.mxGeometry;
import com.mxgraph.model.mxIGraphModel;
import com.mxgraph.swing.mxGraphComponent;
import com.mxgraph.view.mxGraph;

import java.awt.Dimension;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import multij.tools.IllegalInstantiationException;

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
			
			private int depth = -1;
			
			@Override
			public final Object visit(final Node<?> node) {
				final Object result = this.begin(node);
				
				for (final Node<?> argument : node.getArguments()) {
					final Object argumentVertex = argument.accept(this);
					
					graph.insertEdge(parent, null, "", argumentVertex, result);
				}
				
				return this.end(result);
			}
			
			@Override
			public final Object visit(final Zipping node) {
				final Object result = this.begin(node);
				
				graphModel.setValue(result, graphModel.getValue(result) + "\n" + node.getFunctionName());
				
				final Object leftVertex = node.getLeft().accept(this);
				final Object rightVertex = node.getRight().accept(this);
				
				graph.insertEdge(parent, null, "left", leftVertex, result);
				graph.insertEdge(parent, null, "right", rightVertex, result);
				
				return this.end(result);
			}
			
			private final Object begin(final Node<?> node) {
				++this.depth;
				
				depths.put(node, Math.max(this.depth, depths.getOrDefault(node, 0)));
				
				return vertices.computeIfAbsent(node,
						n -> graph.insertVertex(parent, null, n.getClass().getSimpleName() + Arrays.toString(n.getShape()),
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
	
	public static final mxGraphComponent newGraphComponent(final Node<?> node) {
		final int componentWidth = 640;
		final int componentHeight = 480;
		final int cellWidth = 100;
		final int cellHeight = 50;
		final mxGraph graph = newGraph(node, componentWidth, componentHeight,
				cellWidth, cellHeight);
		final mxGraphComponent result = new mxGraphComponent(graph);
		
		result.setPreferredSize(new Dimension(componentWidth, componentHeight));
		
		return result;
	}
	
}
