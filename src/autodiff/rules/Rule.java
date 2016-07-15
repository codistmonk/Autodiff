package autodiff.rules;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public abstract interface Rule<T, R> extends Serializable {
	
	public default boolean test(final T object) {
		return this.test(object, new HashMap<>());
	}
	
	public abstract boolean test(T object, Map<Variable, Object> mapping);
	
	public default R applyTo(final T object) {
		return this.applyTo(object, new HashMap<>());
	}
	
	public abstract R applyTo(T object, Map<Variable, Object> mapping);
	
	public default R applyTo(final T object, final R defaultValue) {
		return this.applyTo(object, new HashMap<>(), defaultValue);
	}
	
	public default R applyTo(final T object, final Map<Variable, Object> mapping, final R defaultValue) {
		return this.test(object, mapping) ? this.applyTo(object, mapping) : defaultValue;
	}
	
}