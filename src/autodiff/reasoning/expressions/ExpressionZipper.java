package autodiff.reasoning.expressions;

import java.io.Serializable;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;

/**
 * @author codistmonk (creation 2015-04-19)
 * 
 * @param <V>
 */
public abstract interface ExpressionZipper<V> extends Serializable, BiFunction<Object, Object, V>, BiConsumer<Object, Object> {
	
	@Override
	public default void accept(final Object expression1, final Object expression2) {
		this.apply(expression1, expression2);
	}
	
	@Override
	public default V apply(final Object expression1, final Object expression2) {
		if (expression1 instanceof List && expression2 instanceof List) {
			return this.visit((List<?>) expression1, (List<?>) expression2);
		}
		
		return this.visit(expression1, expression2);
	}
	
	public abstract V visit(Object expression1, Object expression2);
	
	public default V visit(final List<?> expression1, final List<?> expression2) {
		final int n = expression1.size();
		
		if (n != expression2.size()) {
			return null;
		}
		
		for (int i = 0; i < n; ++i) {
			this.accept(expression1.get(i), expression2.get(i));
		}
		
		return this.visit((Object) expression1, (Object) expression2);
	}
	
}