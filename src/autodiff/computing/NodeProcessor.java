package autodiff.computing;

import java.io.Serializable;

import autodiff.nodes.Node;
import autodiff.nodes.NodeVisitor;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract interface NodeProcessor extends Serializable {
	
	public abstract NodeVisitor<Void> getForwarder();
	
	public abstract NodeVisitor<Void> getBackwardDiffer();
	
	public abstract <N extends Node<?>> N fill(N node, float value);
	
	public abstract <N extends Node<?>> N fullForward(N node);
	
	public abstract <N extends Node<?>> N fullBackwardDiff(N node);
	
}
