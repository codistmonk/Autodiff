package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.cast;

import autodiff.reasoning.expressions.ExpressionZipper;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class Substitution extends Proof.Abstract {
	
	private Object target;
	
	private final Map<Object, Object> equalities;
	
	private final Collection<Integer> indices;
	
	public Substitution(final Object target, final Map<Object, Object> equalities, final Collection<Integer> indices) {
		this(null, target, equalities, indices);
	}
	
	public Substitution(final String provedPropositionName, final Object target,
			final Map<Object, Object> equalities, final Collection<Integer> indices) {
		super(provedPropositionName, Arrays.asList("By substituting in", target, "using", equalities, "at", null));
		this.target = target;
		this.equalities = equalities;
		this.indices = indices instanceof TreeSet ? indices : new TreeSet<>(indices);
		
		this.getMessage().set(5, this.getIndices());
	}
	
	public final Object getTarget() {
		return this.target;
	}
	
	public final Map<Object, Object> getEqualities() {
		return this.equalities;
	}
	
	public final Collection<Integer> getIndices() {
		return this.indices;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final Object substitution = $(this.getTarget(),
				GIVEN, join(AND, iterable(
						this.getEqualities().entrySet().stream().map(e -> $equality(e.getKey(), e.getValue())))),
				AT, new ArrayList<>(this.getIndices()));
		final Object substituted = substituteIn(this.getTarget(), this.getEqualities(), this.getIndices());
		
		return $equality(substitution, substituted);
	}
	
	private static final long serialVersionUID = -5039934017175763847L;
	
	public static final Object substituteIn(final Object target,
			final Map<Object, Object> equalities, final Collection<Integer> indices) {
		return substituteIn(target, equalities, indices, new int[] { -1 });
	}
	
	private static final Object substituteIn(final Object target,
			final Map<Object, Object> equalities, final Collection<Integer> indices, final int[] index) {
		Object replacement = null;
		
		for (final Map.Entry<Object, Object> entry : equalities.entrySet()) {
			if (new ExpressionEquality().apply(entry.getKey(), target)) {
				replacement = entry.getValue();
				break;
			}
		}
		
		if (replacement != null && (indices.isEmpty() || indices.contains(++index[0]))) {
			return replacement;
		}
		
		if (target instanceof List) {
			return list(target).stream().map(e ->
					substituteIn(e, equalities, indices, index)).collect(toList());
		}
		
		return target;
	}
	
	/**
	 * @author codistmonk (creation 2016-08-11)
	 */
	public static final class ExpressionEquality implements ExpressionZipper<Boolean> {
		
		private final Collection<Object> bound = new HashSet<>();
		
		@Override
		public final Boolean visit(final Object expression1, final Object expression2) {
			if (expression1.equals(expression2)) {
				return true;
			}
			
			{
				final Number n1 = cast(Number.class, expression1);
				final Number n2 = cast(Number.class, expression2);
				
				if (n1 != null && n2 != null && n1.toString().equals(n2.toString())) {
					return true;
				}
			}
			
			if (isBlock(expression1) && isBlock(expression2)) {
				final Object v1 = variable(expression1);
				final Object s1 = scope(expression1);
				final Object v2 = variable(expression2);
				final Object s2 = scope(expression2);
				
				if (!deepContains(s1, v2) && !deepContains(s2, v1)) {
					if (this.bound.add(v1)) {
						try {
							return this.apply(s1, substituteIn(s2, map(v2, v1), Collections.emptyList()));
						} finally {
							this.bound.remove(v1);
						}
					}
				}
			}
			
			return false;
		}
		
		@Override
		public final Boolean visit(final List<?> expression1, final List<?> expression2) {
			final int n = expression1.size();
			
			if (n != expression2.size()) {
				return false;
			}
			
			boolean result = true;
			
			for (int i = 0; i < n; ++i) {
				result = this.apply(expression1.get(i), expression2.get(i));
				
				if (!result) {
					break;
				}
			}
			
			return result || this.visit((Object) expression1, (Object) expression2);
		}
		
		private static final long serialVersionUID = 1097894997336832052L;
		
		public static final boolean deepContains(final Object haystack, final Object needle) {
			if (haystack.equals(needle)) {
				return true;
			}
			
			{
				final Iterable<?> objects = cast(Iterable.class, haystack);
				
				if (objects != null) {
					for (final Object object : objects) {
						if (deepContains(object, needle)) {
							return true;
						}
					}
				}
			}
			
			{
				final Object[] objects = cast(Object[].class, haystack);
				
				if (objects != null) {
					for (final Object object : objects) {
						if (deepContains(object, needle)) {
							return true;
						}
					}
				}
			}
			
			return false;
		}
		
	}
	
}