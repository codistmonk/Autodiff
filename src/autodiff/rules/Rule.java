package autodiff.rules;

import java.io.Serializable;
import java.util.Map;
import java.util.function.BiFunction;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public abstract interface Rule<T, R> extends Serializable, BiFunction<T, Map<Variable, Object>, Rules.Result<R>> {
	
	// Deliberately left empty
	
}