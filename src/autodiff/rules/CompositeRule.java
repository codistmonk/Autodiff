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
public final class CompositeRule<T, R> implements Rule<T, R> {
	
	private final Predicate<T> predicate;
	
	private final Application<T, R> application;
	
	public CompositeRule(final Predicate<T> predicate, final Application<T, R> application) {
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
		return this.getPredicate().test(object, mapping) ?
				new Result<>(this.getApplication().apply(object, mapping)) : null;
	}
	
	private static final long serialVersionUID = -7416281112771134372L;
	
}