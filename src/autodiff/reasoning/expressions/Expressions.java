package autodiff.reasoning.expressions;

import static java.util.stream.Collectors.toCollection;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.cast;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.stream.Collector;
import java.util.stream.Stream;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2015-04-19)
 */
public final class Expressions {
	
	private Expressions() {
		throw new IllegalInstantiationException();
	}
	
	public static final Object FORALL = $("∀");
	
	public static final Object IMPLIES = $("⇒");
	
	public static final Object EQUALS = $("=");
	
	public static final Object GIVEN = $("|");
	
	public static final Object REPLACED_BY = $(Special.REPLACED_BY);
	
	public static final Object AND = $(",");
	
	public static final Object AT = $("@");
	
	public static final Object EQUIV = $("⇔");
	
	public static final Object LAND = $("∧");
	
	public static final Object LOR = $("∨");
	
	public static final Object LNOT = $("¬");
	
	public static final Object IN = $("∈");
	
	public static final Object LE = $("≤");
	
	public static final Object GE = $("≥");
	
	private static final Map<Object, Object> globals = new IdentityHashMap<>();
	
	@Deprecated
	public static final void setGlobal(final Object key, final Object value) {
		globals.put(key, value);
	}
	
	@Deprecated
	public static final Object getGlobal(final Object key) {
		return globals.get(key);
	}
	
	public static final boolean asBoolean(final Object object) {
		final Boolean b = cast(Boolean.class, object);
		
		return b != null && b;
	}
	
	public static final Object $new(final String name) {
		return $(new Id(name));
	}
	
	public static final Object $(final Object... objects) {
		if (objects.length == 1) {
			return $n(objects[0]);
		}
		
		if (objects.length == 0) {
			return Collections.emptyList();
		}
		
		return Arrays.stream(objects).map(Expressions::$).collect(toList());
	}
	
	public static final BigDecimal $N(final Object object) {
		return cast(BigDecimal.class, $n(object));
	}
	
	@SuppressWarnings("unchecked")
	public static final <T> T $n(final Object object) {
		if (object instanceof BigDecimal) {
			return (T) object;
		}
		
		if (object instanceof Number) {
			return (T) new BigDecimal(object.toString());
		}
		
		return (T) object;
	}
	
	public static final List<Object> $1(final Object object) {
		final Object o = $n(object);
		
		return Arrays.asList(o);
	}
	
	public static final List<Object> $forall(final Object variableOrName) {
		return list($(FORALL, $(variableOrName)));
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> $forall(final Object... variableOrNamesFollowedByScoped) {
		final int n = variableOrNamesFollowedByScoped.length;
		
		if (n == 1) {
			return $forall(variableOrNamesFollowedByScoped[0]);
		}
		
		Object result = $(variableOrNamesFollowedByScoped[n - 1]);
		
		for (int i = n - 2; 0 <= i; --i) {
			result = $($forall(variableOrNamesFollowedByScoped[i]), result);
		}
		
		return (List<Object>) result;
	}
	
	public static final List<Object> $equality(final Object left, final Object right) {
		return list($(left, EQUALS, right));
	}
	
	public static final List<Object> $replacement(final Object left, final Object right) {
		return list($(left, REPLACED_BY, right));
	}
	
	public static final List<Object> $list(final Object... objects) {
		final List<Object> result = new ArrayList<>();
		
		for (final Object object : objects) {
			result.add($(object));
		}
		
		return result;
	}
	
	public static final Object $rule(final Object... propositions) {
		return $rightAssociativeOperation(IMPLIES, propositions);
	}
	
	public static final Object $rightAssociativeOperation(final Object operator, final Object... operands) {
		final int n = operands.length;
		Object result = operands[n - 1];
		
		for (int i = n - 2; 0 <= i; --i) {
			result = $(operands[i], operator, result);
		}
		
		return result;
	}
	
	public static final List<Object> join(final Object separator, final Object... objects) {
		return join(separator, Arrays.asList(objects));
	}
	
	public static final List<Object> join(final Object separator, final Iterable<Object> objects) {
		final Collection<?> collection = cast(Collection.class, objects);
		final List<Object> result = collection == null ? new ArrayList<>() : new ArrayList<>(2 * collection.size() + 1);
		final Iterator<Object> i = objects.iterator();
		
		if (i.hasNext()) {
			result.add(i.next());
			
			while (i.hasNext()) {
				result.add(separator);
				result.add(i.next());
			}
		}
		
		return result;
	}
	
	public static final Object joinOr1(final Object separator, final Iterable<Object> objects) {
		final Collection<?> collection = cast(Collection.class, objects);
		
		if (collection != null && collection.size() == 1) {
			return objects.iterator().next();
		}
		
		return join(separator, objects);
	}
	
	@SuppressWarnings("unchecked")
	public static final <K, V> Map<K, V> map(final Object... keyAndValues) {
		final Map<K, V> result = new LinkedHashMap<>();
		final int n = keyAndValues.length;
		
		for (int i = 0; i < n; i += 2) {
			result.put((K) keyAndValues[i + 0], (V) keyAndValues[i + 1]);
		}
		
		
		return result;
	}
	
	@SuppressWarnings("unchecked")
	public static final <E> List<E> indices(final int... indices) {
		return (List<E>) Arrays.stream(indices).mapToObj(Integer::valueOf).collect(toList());
	}
	
	public static final <T> Iterable<T> iterable(final Stream<T> stream) {
		return () -> stream.iterator();
	}
	
	public static final void checkArgument(final boolean check, final String message) {
		if (!check) {
			throw new IllegalArgumentException(message);
		}
	}
	
	public static final void checkState(final boolean check, final String message) {
		if (!check) {
			throw new IllegalStateException(message);
		}
	}
	
	public static final boolean isRule(final Object object) {
		final List<?> expression = cast(List.class, object);
		
		return expression != null
				&& expression.size() == 3
				&& IMPLIES.equals(expression.get(1));
	}
	
	public static final Object condition(final Object rule) {
		return list(rule).get(0);
	}
	
	public static final Object conclusion(final Object rule) {
		return list(rule).get(2);
	}
	
	public static final boolean isEquality(final Object object) {
		final List<?> expression = cast(List.class, object);
		
		return expression != null
				&& expression.size() == 3
				&& EQUALS.equals(expression.get(1));
	}
	
	public static final Object left(final Object binaryOperation) {
		return list(binaryOperation).get(0);
	}
	
	public static final Object middle(final Object binaryOperation) {
		return list(binaryOperation).get(1);
	}
	
	public static final Object operator(final Object binaryOperation) {
		return middle(binaryOperation);
	}
	
	public static final Object right(final Object binaryOperation) {
		return list(binaryOperation).get(2);
	}
	
	public static final Object first(final Object pair) {
		return list(pair).get(0);
	}
	
	public static final Object second(final Object pair) {
		return list(pair).get(1);
	}
	
	public static final Object third(final Object pair) {
		return list(pair).get(2);
	}
	
	public static final boolean isSubstitution(final Object object) {
		final List<?> expression = cast(List.class, object);
		
		return expression != null
				&& expression.size() == 5
				&& GIVEN.equals(expression.get(1))
				&& AT.equals(expression.get(3));
	}
	
	public static final Object target(final Object substitution) {
		return list(substitution).get(0);
	}
	
	public static final Object equalities(final Object substitution) {
		return list(substitution).get(2);
	}
	
	public static final Object indices(final Object substitution) {
		return list(substitution).get(4);
	}
	
	public static final boolean isQuantification(final Object object) {
		final List<?> expression = cast(List.class, object);
		
		return expression != null
				&& expression.size() == 2
				&& FORALL.equals(expression.get(0));
	}
	
	public static final Object variable(final Object block) {
		return quantifiedVariable(quantification(block));
	}
	
	public static final Object quantifiedVariable(final Object quantitication) {
		return list(quantitication).get(1);
	}
	
	public static final boolean isBlock(final Object object) {
		final List<?> expression = cast(List.class, object);
		
		return expression != null
				&& expression.size() == 2
				&& isQuantification(expression.get(0));
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> quantification(final Object block) {
		final Object result = list(block).get(0);
		
		checkArgument(isQuantification(result), "Not a quantification: " + result);
		
		return (List<Object>) result;
	}
	
	public static final Object scope(final Object block) {
		return list(block).get(1);
	}
	
	public static final boolean isUltimate(final Object expression) {
		return !isBlock(expression) && !isRule(expression);
	}
	
	public static final Object ultimate(final Object expression) {
		if (isBlock(expression)) {
			return ultimate(scope(expression));
		}
		
		if (isRule(expression)) {
			return ultimate(conclusion(expression));
		}
		
		return expression;
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> list(final Object object) {
		return (List<Object>) object;
	}
	
    public static final <T> Collector<T, ?, TreeSet<T>> toTreeSet() {
        return toCollection(TreeSet::new);
    }
	
	public static final String deepJoin(final String separator, final Object object) {
		final Iterable<?> objects = cast(Iterable.class, object);
		
		if (objects == null) {
			return "" + object;
		}
		
		final StringBuilder resultBuilder = new StringBuilder();
		boolean first = true;
		
		for (final Object o : objects) {
			final Iterable<?> subobjects = cast(Iterable.class, o);
			
			if (first) {
				first = false;
			} else {
				resultBuilder.append(separator);
			}
			
			resultBuilder.append(subobjects == null ? o : deepJoin(separator, subobjects));
		}
		
		return resultBuilder.toString();
	}
	
	/**
	 * @author codistmonk (creation 2016-09-07)
	 */
	public static enum Special {
		
		REPLACED_BY("=");
		
		private final String string;
		
		private Special(final String string) {
			this.string = string;
		}
		
		@Override
		public final String toString() {
			return this.string;
		}
		
	}
	
}
