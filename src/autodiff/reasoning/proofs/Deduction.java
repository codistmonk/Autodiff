package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static java.util.Collections.unmodifiableSet;
import static multij.tools.Tools.last;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class Deduction extends Proof.Abstract {
	
	private final Deduction parent;
	
	private final Collection<Object> parameters;
	
	private final Map<String, Object> propositions;
	
	private final List<String> propositionNames;
	
	private final Map<String, Proof> proofs;
	
	public Deduction(final Deduction parent) {
		this(parent, parent == null ? "" : null);
	}
	
	public Deduction(final Deduction parent, final String provedPropositionName) {
		super(provedPropositionName, new ArrayList<>(Arrays.asList("By deduction in", null, "step(s)")));
		this.parent = parent;
		this.parameters = new LinkedHashSet<>();
		this.propositions = new HashMap<>();
		this.propositionNames = new ArrayList<>();
		this.proofs = new HashMap<>();
		
		this.getMessage().set(1, new Object() {
			
			@Override
			public final String toString() {
				return Integer.toString(getProofs().size());
			}
			
		});
		
		checkArgument(provedPropositionName != null,
				"Invalid proposition name: " + provedPropositionName);
		checkArgument(parent == null || parent.getProposition(provedPropositionName) == null,
				"Duplicate proposition name: " + provedPropositionName);
	}
	
	public final Deduction getParent() {
		return this.parent;
	}
	
	public final Collection<Object> getParameters() {
		return this.parameters;
	}
	
	public final Map<String, Object> getPropositions() {
		return this.propositions;
	}
	
	public final List<String> getPropositionNames() {
		return this.propositionNames;
	}
	
	public final String newPropositionName() {
		return this.getProvedPropositionName() + "." + (this.getPropositions().size() + 1);
	}
	
	public final String getPropositionName(final int index) {
		checkArgument(index < 0, "Not negative: " + index);
		
		final int i = this.getPropositionNames().size() + index;
		
		return 0 <= i ? this.getPropositionNames().get(i) : this.getParent().getPropositionName(i);
	}
	
	public final Map<String, Proof> getProofs() {
		return this.proofs;
	}
	
	public final Object getProposition(final String propositionName) {
		final Object candidate = this.getPropositions().get(propositionName);
		
		return candidate != null || this.getParent() == null ? candidate : this.getParent().getProposition(propositionName);
	}
	
	public final Deduction forall(final Object parameter) {
		if (!this.getParameters().add(parameter)) {
			throw new IllegalArgumentException();
		}
		
		return this;
	}
	
	public final Deduction suppose(final String propositionName, final Object proposition) {
		checkArgument(propositionName != null, "Invalid proposition name: " + propositionName);
		checkArgument(this.getProposition(propositionName) == null, "Duplicate proposition name: " + propositionName);
		
		this.getPropositions().put(propositionName, proposition);
		this.getPropositionNames().add(propositionName);
		
		return this;
	}
	
	public final Deduction conclude() {
		if (this.getParent() != null) {
			this.getParent().conclude(this);
		}
		
		return this;
	}
	
	public final Deduction conclude(final Proof proof) {
		if (!PRIMITIVE_PROOFS.contains(proof.getClass())) {
			return proof.concludeIn(this);
		}
		
		String provedPropositionName = proof.getProvedPropositionName();
		
		if (provedPropositionName == null) {
			provedPropositionName = this.newPropositionName();
		}
		
		this.suppose(provedPropositionName, proof.getProvedPropositionFor(this));
		this.getProofs().put(provedPropositionName, proof);
		
		return this;
	}
	
	public final List<String> getConditionNames() {
		final List<String> result = new ArrayList<>(this.getPropositionNames());
		
		result.removeAll(this.getProofs().keySet());
		
		return result;
	}
	
	public final List<String> getConclusionNames() {
		final List<String> result = new ArrayList<>(this.getPropositionNames());
		
		result.retainAll(this.getProofs().keySet());
		
		return result;
	}
	
	public final Object getProvedProposition() {
		return this.getProvedPropositionFor(this);
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		checkArgument(!this.getConclusionNames().isEmpty(), "Nothing to conclude");
		
		final Object conclusion = this.getProposition(last(this.getConclusionNames()));
		Object result = conclusion;
		
		{
			final List<String> conditionNames = this.getConditionNames();
			
			for (final ListIterator<String> i = conditionNames.listIterator(conditionNames.size()); i.hasPrevious();) {
				result = $rule(this.getProposition(i.previous()), result);
			}
		}
		
		{
			final List<Object> parameters = new ArrayList<>(this.getParameters());
			
			for (final ListIterator<Object> i = parameters.listIterator(parameters.size()); i.hasPrevious();) {
				result = $forall(i.previous(), result);
			}
		}
		
		return result;
	}
	
	private static final long serialVersionUID = -1040410980387761070L;
	
	@SuppressWarnings("unchecked")
	public static final Collection<Class<? extends Proof>> PRIMITIVE_PROOFS = unmodifiableSet(Tools.set(
			ModusPonens.class, Substitution.class, Binding.class,
			BasicNumericVerification.class,
			Deduction.class));
	
}