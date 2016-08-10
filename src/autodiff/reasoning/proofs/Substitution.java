package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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
		final Object replacement = equalities.get(target);
		
		if (replacement != null && (indices.isEmpty() || indices.contains(++index[0]))) {
			return replacement;
		}
		
		if (target instanceof List) {
			return list(target).stream().map(e ->
					substituteIn(e, equalities, indices, index)).collect(toList());
		}
		
		return target;
	}
	
}