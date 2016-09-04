package autodiff.rules;

import java.io.Serializable;
import java.util.Map;
import java.util.function.BiFunction;

import autodiff.rules.Rules.Result;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
@Deprecated
public abstract interface Rule<T, R> extends Serializable, BiFunction<T, Map<Variable, Object>, Rules.Result<R>> {
	
	@Override
	public default Result<R> apply(final T t, final Map<Variable, Object> u) {
		return this.test(t, u) ? new Result<>(this.applyTo(t, u)) : null;
	}
	
	public abstract boolean test(T object, Map<Variable, Object> mapping);
	
	public abstract R applyTo(T object, Map<Variable, Object> mapping);
	
}