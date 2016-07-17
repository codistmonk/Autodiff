package autodiff.computing;

import static multij.tools.Tools.debugPrint;

import autodiff.cl.CLContext;
import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;

import java.util.Collection;
import java.util.LinkedHashSet;

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
		final Collection<Node<?>> nodes = node.collectTo(new LinkedHashSet<>());
		
		debugPrint(nodes);
		
		// TODO Auto-generated method stub
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
