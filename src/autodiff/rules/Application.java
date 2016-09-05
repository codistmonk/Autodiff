package autodiff.rules;

import java.io.Serializable;
import java.util.Map;
import java.util.function.BiFunction;

/**
 * @author codistmonk (creation 2016-09-05)
 *
 * @param <T>
 * @param <R>
 */
public abstract interface Application<T, R> extends Serializable, BiFunction<T, Map<Variable, Object>, R> {
	// Deliberately left empty
}