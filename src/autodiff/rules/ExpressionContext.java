package autodiff.rules;

import static java.util.stream.Collectors.toCollection;

import java.io.Serializable;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;

import autodiff.rules.SimpleRule.Application;
import autodiff.rules.SimpleRule.Predicate;

/**
 * @author codistmonk (creation 2015-12-07)
 */
public final class ExpressionContext implements Serializable {
	
	private final Rules<Object, Object> typeRules = new Rules<>();
	
	private final Rules<Object, Object> simplificationRules = new Rules<>();
	
	public final Rules<Object, Object> getTypeRules() {
		return this.typeRules;
	}
	
	public final Rules<Object, Object> getSimplificationRules() {
		return this.simplificationRules;
	}
	
	public final Object simplify(final Object expression) {
		return this.getSimplificationRules().applyTo(expression, expression);
	}
	
	public final Object getTypeOf(final Object expression) {
		return this.getTypeRules().applyTo(expression, "Undefined");
	}
	
	public final Object $(final Object... objects) {
		return this.simplify(Arrays.stream(objects).map(ExpressionContext::expression).collect(toCollection(ArrayList::new)));
	}
	
	public final void declare(final Object object, final Object type) {
		this.getTypeRules().add((e, m) -> Variable.match(object, e, m), (e, m) -> Variable.rewrite(type, m));
	}
	
	public final void addType(final Predicate<Object> predicate, final Application<Object, Object> application) {
		this.addType(new SimpleRule<>(predicate, application));
	}
	
	public final void addType(final Rule<Object, Object> rule) {
		this.getTypeRules().add(rule);
	}
	
	public final void addSimplification(final Predicate<Object> predicate, final Application<Object, Object> application) {
		this.addSimplification(new SimpleRule<>(predicate, application));
	}
	
	public final void addSimplification(final Rule<Object, Object> rule) {
		this.getSimplificationRules().add(rule);
	}
	
	private static final long serialVersionUID = 2516111889161000383L;
	
	public static final BigDecimal number(final Object object) {
		if (object instanceof BigDecimal) {
			return (BigDecimal) object;
		}
		
		if (object instanceof Byte || object instanceof Short || object instanceof Integer || object instanceof Long) {
			return BigDecimal.valueOf(((Number) object).longValue());
		}
		
		if (object instanceof Float || object instanceof Double) {
			return BigDecimal.valueOf(((Number) object).doubleValue());
		}
		
		if (object instanceof Number) {
			return new BigDecimal(object.toString());
		}
		
		return null;
	}
	
	public static final Object expression(final Object object) {
		final Object number = number(object);
		
		return number == null ? object : number;
	}
	
}