package autodiff.rules;

import java.util.Map;
import java.util.function.BiFunction;

import autodiff.rules.Rules.Result;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public final class SimpleRule<T, R> implements Rule<T, R> {
	
	private final Predicate<T> predicate;
	
	private final BiFunction<T, Map<Variable, Object>, R> application;
	
	public SimpleRule(final Predicate<T> predicate, final BiFunction<T, Map<Variable, Object>, R> application) {
		this.predicate = predicate;
		this.application = application;
	}
	
	public final Predicate<T> getPredicate() {
		return this.predicate;
	}
	
	public final BiFunction<T, Map<Variable, Object>, R> getApplication() {
		return this.application;
	}
	@Override
	public final Result<R> apply(final T object, final Map<Variable, Object> mapping) {
		return this.test(object, mapping) ? new Result<>(this.applyTo(object, mapping)) : null;
	}
	
	private final boolean test(final T object, final Map<Variable, Object> mapping) {
		return this.getPredicate().test(object, mapping);
	}
	
	private final R applyTo(final T object, final Map<Variable, Object> mapping) {
		return this.getApplication().apply(object, mapping);
	}
	
	private static final long serialVersionUID = -7416281112771134372L;
	
}