package autodiff.reasoning.expressions;

import java.io.Serializable;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * @author codistmonk (creation 2015-04-17)
 * 
 * @param <V>
 */
public abstract interface ExpressionVisitor<V> extends Serializable, Function<Object, V>, Consumer<Object> {
	
	@Override
	public default void accept(final Object expression) {
		this.apply(expression);
	}
	
	@Override
	public default V apply(final Object expression) {
		if (expression instanceof List) {
			return this.visit((List<?>) expression);
		}
		
		return this.visit(expression);
	}
	
	public abstract V visit(Object expression);
	
	public default V visit(final List<?> expression) {
		expression.forEach(this);
		
		return this.visit((Object) expression);
	}
	
}