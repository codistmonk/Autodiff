package autodiff.nodes;

import static multij.tools.Tools.ignore;

import java.io.Serializable;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public abstract interface NodeVisitor<V> extends Serializable {
	
	public default V visit(final Node<?> node) {
		ignore(node);
		
		return null;
	}
	
	public default V visit(final ShapeNode node) {
		return this.visit((Node<?>) node);
	}
	
	public default V visit(final AbstractNode<?> node) {
		return this.visit((Node<?>) node);
	}
	
	public default V visit(final UnaryNode<?> node) {
		return this.visit((AbstractNode<?>) node);
	}
	
	public default V visit(final BinaryNode<?> node) {
		return this.visit((AbstractNode<?>) node);
	}
	
	public default V visit(final Data node) {
		return this.visit((AbstractNode<?>) node);
	}
	
	public default V visit(final Mapping node) {
		return this.visit((UnaryNode<?>) node);
	}
	
	public default V visit(final Zipping node) {
		return this.visit((BinaryNode<?>) node);
	}
	
	public default V visit(final MatrixMultiplication node) {
		return this.visit((BinaryNode<?>) node);
	}
	
}
