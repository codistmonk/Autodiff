package autodiff.rules;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import autodiff.rules.SimpleRule.Application;
import autodiff.rules.SimpleRule.Predicate;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public final class Rules<T, R> implements Rule<T, R> {
	
	private final List<Rule<T, R>> rules = new ArrayList<>();
	
	public final List<Rule<T, R>> getRules() {
		return this.rules;
	}
	
	public final void add(final Predicate<T> predicate, final Application<T, R> application) {
		this.add(new SimpleRule<>(predicate, application));
	}
	
	public final void add(final Rule<T, R> rule) {
		this.getRules().add(rule);
	}
	
	@Override
	public final boolean test(final T object, final Map<Variable, Object> mapping) {
		return this.findRuleFor(object, mapping) != null;
	}
	
	@Override
	public final R applyTo(final T object, final Map<Variable, Object> mapping) {
		return this.findRuleFor(object, mapping).applyTo(object, mapping);
	}
	
	@Override
	public final R applyTo(final T object, final Map<Variable, Object> mapping, final R defaultValue) {
		final Rule<T, R> rule = this.findRuleFor(object, mapping);
		
		return rule != null ? rule.applyTo(object, mapping) : defaultValue;
	}
	
	public final Rule<T, R> findRuleFor(final T object, final Map<Variable, Object> mapping) {
		final Map<Variable, Object> backup = new LinkedHashMap<>(mapping);
		
		for (final Rule<T, R> rule : this.rules) {
			mapping.clear();
			mapping.putAll(backup);
			
			if (rule.test(object, mapping)) {
				return rule;
			}
		}
		
		return null;
	}
	
	private static final long serialVersionUID = 271358038357056552L;
	
}