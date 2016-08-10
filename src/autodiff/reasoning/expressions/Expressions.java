package autodiff.reasoning.expressions;

import static java.util.stream.Collectors.toCollection;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.cast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
	
	public static final String FORALL = $("∀");
	
	public static final String IMPLIES = $("⇒");
	
	public static final String EQUALS = $("=");
	
	public static final String GIVEN = $("|");
	
	public static final String AND = $(",");
	
	public static final String AT = $("@");
	
	public static final Object $new(final String name) {
		return $(new Id(name));
	}
	
	@SuppressWarnings("unchecked")
	public static final <T> T $(final Object... objects) {
		if (objects.length == 1) {
			return (T) objects[0];
		}
		
		if (objects.length <= 1) {
			return (T) Arrays.asList(objects);
		}
		
		return (T) Arrays.stream(objects).map(Expressions::$).collect(toList());
	}
	
	public static final List<Object> $forall(final Object variableOrName) {
		return $(FORALL, $(variableOrName));
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
		return $(left, EQUALS, right);
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
	
	public static final Object right(final Object binaryOperation) {
		return list(binaryOperation).get(2);
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
		
}
