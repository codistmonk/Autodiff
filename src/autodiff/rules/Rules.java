package autodiff.rules;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

import autodiff.rules.SimpleRule.Application;
import autodiff.rules.SimpleRule.Predicate;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public final class Rules<T, R> implements Rule<T, R>, BiFunction<T, Map<Variable, Object>, Rules.Result<R>> {
	
	private final List<BiFunction<T, Map<Variable, Object>, Result<R>>> rules = new ArrayList<>();
	
	public final List<BiFunction<T, Map<Variable, Object>, Result<R>>> getRules() {
		return this.rules;
	}
	
	public final R apply(final T input) {
		return this.apply(input, new LinkedHashMap<>()).get();
	}
	
	@Override
	public final Result<R> apply(final T input, final Map<Variable, Object> mapping) {
		final Map<Variable, Object> backup = new LinkedHashMap<>(mapping);
		
		for (final BiFunction<T, Map<Variable, Object>, Result<R>> rule : this.getRules()) {
			restore(backup, mapping);
			
			final Result<R> r = rule.apply(input, mapping);
			
			if (r != null) {
				return r;
			}
		}
		
		return null;
	}
	
	public final Rules<T, R> add(final BiFunction<T, Map<Variable, Object>, Result<R>> rule) {
		this.getRules().add(rule);
		
		return this;
	}
	
	@Deprecated
	public final void add(final Predicate<T> predicate, final Application<T, R> application) {
		this.add(new SimpleRule<>(predicate, application));
	}
	
	@Override
	@Deprecated
	public final boolean test(final T object, final Map<Variable, Object> mapping) {
		throw new RuntimeException();
	}
	
//	@Override
	@Deprecated
	public final R applyTo(final T object, final Map<Variable, Object> mapping) {
		return this.apply(object, mapping).get();
	}
	
	private static final long serialVersionUID = 271358038357056552L;
	
	public static final void restore(final Map<Variable, Object> backup, final Map<Variable, Object> mapping) {
		mapping.forEach((k, v) -> k.set(null));
		mapping.clear();
		mapping.putAll(backup);
		mapping.forEach(Variable::set);
	}
	
	/**
	 * @author codistmonk (creation 2016-09-04)
	 *
	 * @param <R>
	 */
	public static final class Result<R> implements Serializable {
		
		private final R value;
		
		public Result(final R value) {
			this.value = value;
		}
		
		public final R get() {
			return this.value;
		}
		
		private static final long serialVersionUID = -4189453873936338637L;
		
	}
	
}