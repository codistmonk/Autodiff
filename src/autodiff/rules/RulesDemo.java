package autodiff.rules;

import static autodiff.rules.ExpressionContext.number;
import static multij.tools.Tools.debugPrint;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2015-12-07)
 */
public final class RulesDemo {
	
	private RulesDemo() {
		throw new IllegalInstantiationException();
	}
	
	/**
	 * @param commandLineArguments
	 * <br>Unused
	 */
	public static final void main(final String... commandLineArguments) {
		final ExpressionContext context = new ExpressionContext();
		
		context.addType((e, m) -> number(e) != null, (e, m) -> "Scalar");
		context.addSimplification(isNumberBinaryOperation("+"), numberBinaryOperation(BigDecimal::add));
		context.addSimplification(isNumberBinaryOperation("*"), numberBinaryOperation(BigDecimal::multiply));
		context.addSimplification((e, m) -> isScalarBinaryOperation("+", e, context) && left(e).equals(right(e)), (e, m) -> context.$(2, "*", left(e)));
		context.addSimplification((e, m) -> isScalarBinaryOperation("*", e, context) && left(e).equals(right(e)), (e, m) -> context.$(left(e), "^", 2));
		
		debugPrint(context.getTypeOf(42));
		debugPrint(context.getTypeOf("toto"));
		debugPrint(context.$(1, "+", 2));
		
		debugPrint(context.$("a", "+", "a"));
		
		context.declare("a", "Scalar");
		
		debugPrint(context.$("a", "+", "a"));
		debugPrint(context.$("a", "*", "a"));
	}
	
	public static final boolean isScalarBinaryOperation(final Object operator, final Object expression, final ExpressionContext context) {
		return isBinaryOperation(operator, expression) && "Scalar".equals(context.getTypeOf(left(expression))) && "Scalar".equals(context.getTypeOf(right(expression)));
	}
	
	public static final <T> T right(final Object expression) {
		return get(expression, 2);
	}
	
	public static final <T> T left(final Object expression) {
		return get(expression, 0);
	}
	
	public static final BiFunction<Object, Map<Variable, Object>, Object> numberBinaryOperation(final BiFunction<BigDecimal, BigDecimal, BigDecimal> operation) {
		return (e, m) -> operation.apply(number(left(e)), number(right(e)));
	}
	
	public static final Predicate<Object> isNumberBinaryOperation(final Object operator) {
		return (e, m) -> isNumberBinaryOperation(operator, e);
	}
	
	public static final boolean isNumberBinaryOperation(final Object operator, final Object expression) {
		return isBinaryOperation(operator, expression) && isNumber(left(expression)) && isNumber(right(expression));
	}
	
	public static final boolean isBinaryOperation(final Object operator, final Object expression) {
		return isList(expression) && size(expression) == 3 && operator.equals(get(expression, 1));
	}
	
	public static final boolean isNumber(final Object object) {
		return number(object) != null;
	}
	
	public static final boolean isList(final Object object) {
		return object instanceof List;
	}
	
	@SuppressWarnings("unchecked")
	public static final <T> T get(final Object object, final int index) {
		return ((List<T>) object).get(index);
	}
	
	public static final int size(final Object object) {
		return ((List<?>) object).size();
	}
	
}
