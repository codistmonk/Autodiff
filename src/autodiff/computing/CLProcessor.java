package autodiff.computing;

import static multij.tools.Tools.cast;
import static multij.tools.Tools.debugPrint;

import autodiff.cl.CLContext;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;
import autodiff.nodes.Selection;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;

/**
 * @author codistmonk (creation 2016-07-17)
 */
public final class CLProcessor implements NodeProcessor {
	
	private final CLContext context;
	
	private final Forwarder forwarder;
	
	private final BackwardDiffer backwardDiffer;
	
	public CLProcessor() {
		this(new CLContext());
	}
	
	public CLProcessor(final CLContext context) {
		this.context = context;
		this.forwarder = this.new Forwarder();
		this.backwardDiffer = this.new BackwardDiffer();
	}
	
	public final CLContext getContext() {
		return this.context;
	}
	
	@Override
	public final NodeVisitor<Void> getForwarder() {
		return this.forwarder;
	}
	
	@Override
	public final NodeVisitor<Void> getBackwardDiffer() {
		return this.backwardDiffer;
	}
	
	@Override
	public final <N extends Node<?>> N fullForward(final N node) {
		final Node<?>[] nodes = node.collectTo(new LinkedHashSet<>()).toArray(new Node[0]);
		
		debugPrint(nodes.length);
		
		final StringBuilder programSourceBuilder = new StringBuilder("__kernel void net(");
		final Map<Node<?>, String> nodeNames = new HashMap<>();
		
		for (int i = 0; i < nodes.length; ++i) {
			final Node<?> n = nodes[i];
			
			if (n instanceof Data) {
				final String nodeName = "data_" + nodeNames.size();
				
				nodeNames.put(n, nodeName);
				
				programSourceBuilder.append("__global float const * const ").append(nodeName).append(", ");
			}
		}
		
		nodeNames.put(node, "result");
		
		programSourceBuilder.append("__global float * const result) {\n");
		
		{
			final Selection selection = cast(Selection.class, node);
			
			if (selection != null) {
				final String vectorsName = nodeNames.get(selection.getVectors());
				final String indicesName = nodeNames.get(selection.getIndices());
				
				debugPrint(vectorsName);
				debugPrint(indicesName);
				
				final int m = selection.getVectors().getLength();
				final int n = selection.getIndices().getLength();
				final int stride = m / n;
				
				programSourceBuilder.append("	for (int i = 0, j = 0; i < ").append(m).append("; i += ").append(stride).append(", ++j) {\n");
				programSourceBuilder.append("		result[j] = ").append(vectorsName).append("[i + ").append(indicesName).append("[j]];\n");
				programSourceBuilder.append("	}\n");
			}
		}
		
		programSourceBuilder.append("}\n");
		
		debugPrint("\n" + programSourceBuilder);
		
		return null;
	}
	
	@Override
	public final <N extends Node<?>> N fullBackwardDiff(final N node) {
		// TODO Auto-generated method stub
		return null;
	}
	
	/**
	 * @author codistmonk (creation 2016-07-17)
	 */
	private final class Forwarder implements NodeVisitor<Void> {
		
		Forwarder() {
			// NOP
		}
		
		private static final long serialVersionUID = 8143280110227329187L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-07-17)
	 */
	private final class BackwardDiffer implements NodeVisitor<Void> {
		
		BackwardDiffer() {
			// NOP
		}
		
		private static final long serialVersionUID = -2609588837130668886L;
		
	}
	
	private static final long serialVersionUID = -7097287103829755831L;
	
	public static final CLProcessor INSTANCE = new CLProcessor();
	
}
