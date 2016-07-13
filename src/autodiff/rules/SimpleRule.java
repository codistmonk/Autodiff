package autodiff.rules;

import java.io.Serializable;
import java.util.Map;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public final class SimpleRule<T, R> implements Rule<T, R> {
	
	private final SimpleRule.Predicate<T> predicate;
	
	private final SimpleRule.Application<T, R> application;
	
	public SimpleRule(final SimpleRule.Predicate<T> predicate, final SimpleRule.Application<T, R> application) {
		this.predicate = predicate;
		this.application = application;
	}
	
	public final SimpleRule.Predicate<T> getPredicate() {
		return this.predicate;
	}
	
	public final SimpleRule.Application<T, R> getApplication() {
		return this.application;
	}
	
	@Override
	public final boolean test(final T object, final Map<Variable, Object> mapping) {
		return this.getPredicate().test(object, mapping);
	}
	
	@Override
	public final R applyTo(final T object, final Map<Variable, Object> mapping) {
		return this.getApplication().applyTo(object, mapping);
	}
	
	private static final long serialVersionUID = -7416281112771134372L;
	
	/**
	 * @author codistmonk (creation 2015-12-07)
	 *
	 * @param <T>
	 */
	public static abstract interface Predicate<T> extends Serializable {
		
		public abstract boolean test(T object, Map<Variable, Object> mapping);
		
	}
	
	/**
	 * @author codistmonk (creation 2015-12-07)
	 *
	 * @param <T>
	 * @param <R>
	 */
	public static abstract interface Application<T, R> extends Serializable {
		
		public abstract R applyTo(T object, Map<Variable, Object> mapping);
		
	}
	
}