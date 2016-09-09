package autodiff.nodes;

import static autodiff.reasoning.deductions.Autodiff.*;
import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.rules.Variable.matchOrFail;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.rules.Variable;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class Computation extends AbstractNode<Computation> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private String typeName;
	
	private Runnable binder;
	
	private Deduction boundForm;
	
	public Computation() {
		super(new ArrayList<>());
		this.bindings = new LinkedHashMap<>();
		this.definition = new ArrayList<>();
	}
	
	@Override
	public final boolean isComputationNode() {
		return true;
	}
	
	public final Map<String, Object> getBindings() {
		return this.bindings;
	}
	
	public final Object get(final String key) {
		return this.getBindings().get(key);
	}
	
	public final Computation set(final String key, final Object value) {
		this.getBindings().put(key, value);
		
		return this;
	}
	
	public final List<Object> getDefinition() {
		return this.definition;
	}
	
	public final Computation setDefinition(final List<Object> definition) {
		this.definition = definition;
		
		return this;
	}
	
	public final String getTypeName() {
		return this.typeName;
	}
	
	public final Computation setTypeName(final String typeName) {
		this.typeName = typeName;
		
		return this;
	}
	
	public final Runnable getBinder() {
		return this.binder;
	}
	
	public final Computation setBinder(final Runnable binder) {
		this.binder = binder;
		
		return this;
	}
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	@Override
	public final String getName() {
		return "[" + this.getId() + "]" + this.getTypeName();
	}
	
	@Override
	public final Computation autoShape() {
		final Deduction deduction = this.getBoundForm();
		final Object proposition = deduction.getProposition(deduction.getPropositionName(-1));
		
		{
			final Variable vX = v("X");
			final Variable vi = v("i");
			final Variable vs = v("s");
			final Variable vn = v("n");
			
			matchOrFail(p(sequence(",", $(p(vX), "_", $(vi, "<", vn)), vs)), right(proposition));
			
			return this.setShape(toInts(flattenSequence(",", vs.get())));
		}
	}
	
	public final Deduction getBoundForm() {
		if (this.boundForm == null) {
			this.boundForm = Basics.build(new Deduction(
					AUTODIFF, this.getName() + "_bind"), this.getBinder(), new Simple(1));
		}
		
		return this.boundForm;
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Computation ones() {
		final Computation result = new Computation().setTypeName("ones");
		
		final Object n = $new("n");
		final Object s = $new("s");
		final Object i = $new("i");
		
		result.setDefinition(
				list($(FORALL, n, IN, POS,
						$(FORALL, s, IN, $(POS, "^", n),
								$($("ones", " ", s), "=", p(sequence(",", $(p(1), "_", $(i, "<", $(PI, s))), s)))))));
		
		result.set("s", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				{
					subdeduction();
					
					final Object[] s = toObjects((int[]) result.get("s"));
					
					autobindTrim(name(-1), $(s.length));
					
					canonicalizeForallIn(name(-1));
					
					bind(name(-1), sequence(",", s));
					
					deduceCartesianProduct(POS, s);
					
					apply(name(-2), name(-1));
					
					{
						final Variable vX = v("X");
						final Variable vi = v("i");
						final Variable vs = v("s");
						final Variable vn = v("n");
						
						matchOrFail(p(sequence(",", $(p(vX), "_", $(vi, "<", vn)), vs)), right(proposition(-1)));
						matchOrFail($(PI, vs), vn.get());
						
						{
							subdeduction();
							
							computeVectorReductionByProduct(vn.get());
							rewrite(name(-2), name(-1));
							
							conclude();
						}
					}
					
					conclude();
				}
			}
			
		});
		
		return result;
	}
	
	public static final Integer[] toObjects(final int... values) {
		final Integer[] result = new Integer[values.length];
		
		for (int i = 0; i < values.length; ++i) {
			result[i] = values[i];
		}
		
		return result;
	}
	
}
