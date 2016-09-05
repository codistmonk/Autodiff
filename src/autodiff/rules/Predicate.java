package autodiff.rules;

import java.io.Serializable;
import java.util.Map;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 */
public abstract interface Predicate<T> extends Serializable {
	
	public abstract boolean test(T object, Map<Variable, Object> mapping);
	
}
