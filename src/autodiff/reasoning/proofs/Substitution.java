package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.*;

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
	
	private final Map<Object, Object> replacements;
	
	private final Collection<Integer> indices;
	
	public Substitution(final Object target, final Map<Object, Object> replacements, final Collection<Integer> indices) {
		this(null, target, replacements, indices);
	}
	
	public Substitution(final String provedPropositionName, final Object target,
			final Map<Object, Object> replacements, final Collection<Integer> indices) {
		super(provedPropositionName, Arrays.asList("By substituting in", target, "using", replacements, "at", null));
		this.target = target;
		this.replacements = replacements;
		this.indices = indices instanceof TreeSet ? indices : new TreeSet<>(indices);
		
		this.getMessage().set(5, this.getIndices());
	}
	
	public final Object getTarget() {
		return this.target;
	}
	
	public final Map<Object, Object> getReplacements() {
		return this.replacements;
	}
	
	public final Collection<Integer> getIndices() {
		return this.indices;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final Object substitution = $(this.getTarget(),
				GIVEN, join(AND, iterable(
						this.getReplacements().entrySet().stream().map(e -> $replacement(e.getKey(), e.getValue())))),
				AT, new ArrayList<>(this.getIndices()));
		final Object substituted = substituteIn(this.getTarget(), this.getReplacements(), this.getIndices());
		
		return $equality(substitution, substituted);
	}
	
	private static final long serialVersionUID = -5039934017175763847L;
	
	public static final Object substituteIn(final Object target,
			final Map<Object, Object> replacements, final Collection<Integer> indices) {
		return substituteIn(target, replacements, indices, new int[] { -1 });
	}
	
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
	
	public static final boolean equal(final Object expression1, final Object expression2) {
		return new ExpressionEquality().apply(expression1, expression2);
	}
	
	private static final Object substituteIn(final Object target,
			final Map<Object, Object> replacements, final Collection<Integer> indices, final int[] index) {
		Object replacement = null;
		
		for (final Map.Entry<Object, Object> entry : replacements.entrySet()) {
			if (equal(entry.getKey(), target)) {
				replacement = entry.getValue();
				break;
			}
		}
		
		if (replacement != null && (indices.isEmpty() || indices.contains(++index[0]))) {
			return replacement;
		}
		
		if (target instanceof List) {
			return list(target).stream().map(e ->
					substituteIn(e, replacements, indices, index)).collect(toList());
		}
		
		return target;
	}
	
	/**
	 * @author codistmonk (creation 2016-08-11)
	 */
	public static abstract class AbstractExpressionEquality implements ExpressionZipper<Boolean> {
		
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
			
			return this.postVisit(expression1, expression2);
		}
		
		@Override
		public final Boolean visit(final List<?> expression1, final List<?> expression2) {
			final int n = expression1.size();
			
			if (n != expression2.size()) {
				return false;
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
			
			for (int i = 0; i < n; ++i) {
				if (!this.apply(expression1.get(i), expression2.get(i))) {
					return false;
				}
			}
			
			return true;
		}
		
		protected boolean postVisit(final Object expression1, final Object expression2) {
			ignore(expression1);
			ignore(expression2);
			
			return false;
		}
		
		private static final long serialVersionUID = 1097894997336832052L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-11)
	 */
	public static final class ExpressionEquality extends AbstractExpressionEquality {
		
		private static final long serialVersionUID = 6883500932984939229L;
		
	}
	
}