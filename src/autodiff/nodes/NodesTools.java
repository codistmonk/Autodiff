package autodiff.nodes;

import static autodiff.computing.Functions.INFIX_OPERATORS;
import static autodiff.computing.Functions.POSTFIX_OPERATORS;
import static autodiff.computing.Functions.PREFIX_OPERATORS;
import static autodiff.computing.Functions.SUM;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.ignore;

import java.util.Arrays;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-15)
 */
public final class NodesTools {
	
	private NodesTools() {
		throw new IllegalInstantiationException();
	}
	
	public static final Node<?> $(final Object... objects) {
		final int n = objects.length;
		
		if (n == 1) {
			final Node<?> node = cast(Node.class, objects[0]);
			
			if (node != null) {
				return node;
			}
		}
		
		try {
			final Node<?> data = new Data().setShape(n);
			
			for (int i = 0; i < n; ++i) {
				data.set(i, ((Number) objects[i]).floatValue());
			}
			
			return data;
		} catch (final Exception exception) {
			ignore(exception);
		}
		
		if (n == 3) {
			if (INFIX_OPERATORS.contains(objects[1])) {
				return new Zipping().setLeft($(objects[0])).setRight($(objects[2])).setFunctionName(objects[1].toString()).autoShape();
			}
			
			if (SUM.equals(objects[0])) {
				return new Sum().setStrides((int[]) objects[1]).setArgument($(objects[2])).autoShape();
			}
			
			if ("@".equals(objects[1])) {
				return new Selection().setLeft($(objects[0])).setRight($(objects[2])).autoShape();
			}
		}
		
		if (n == 2) {
			if (PREFIX_OPERATORS.contains(objects[0])) {
				return new Mapping().setArgument($(objects[1])).setFunctionName(objects[0].toString()).autoShape();
			}
			
			if (POSTFIX_OPERATORS.contains(objects[1])) {
				return new Mapping().setArgument($(objects[0])).setFunctionName(objects[1].toString()).autoShape();
			}
			
			if (SUM.equals(objects[0])) {
				return new Sum().setArgument($(objects[1])).autoShape();
			}
			
			final Node<?> left = cast(Node.class, $(objects[0]));
			final Node<?> right = cast(Node.class, $(objects[1]));
			
			if (left != null && right != null) {
				return new MatrixMultiplication().setLeft(left).setRight(right).autoShape();
			}
		}
		
		throw new IllegalArgumentException(Arrays.toString(objects));
	}
	
}
