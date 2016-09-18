package autodiff.nodes;

import static autodiff.reasoning.deductions.Autodiff.*;
import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalizeLast;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.rules.Variable.matchOrFail;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.ScalarAlgebra;
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
	
	public static final Object ptuple(final Object... objects) {
		return p(tuple(objects));
	}
	
	public static final Computation matrixMultiplication() {
		final String name = "mat_mul";
		final Computation result = new Computation().setTypeName(name);
		
		{
			final Object _l = $new("l");
			final Object _m = $new("m");
			final Object _n = $new("n");
			final Object _A = $new("A");
			final Object _B = $new("B");
			final Object _C = $new("C");
			final Object _i = $new("i");
			final Object _j = $new("j");
			
			final Object _r = floor($(_i, "/", _n));
			final Object _c = $(_i, "%", _n);
			
			result.setDefinition(
					list($(FORALL, _l, ",", _m, ",", _n, IN, POS,
							$(FORALL, _A, IN, $("M", "_", tuple(_l, _m)),
									$(FORALL, _B, IN, $("M", "_", tuple(_m, _n)),
											$(FORALL, _C, IN, $(R, "^", $(_l, "*", _n)),
													$($($(name, _C), tuple(_A, _B)),
															"=", ptuple(
																	$(p($($(_C, "_", _i), "+", $(SUM, "_", $(_j, "<", _m), $($(_A, "_", tuple(_r, _j)), "*", $(_B, "_", tuple(_j, _c)))))), "_", $(_i, "<", $(_l, "*", _n))),
																	tuple(_l, _n)))))))));
		}
		
		result.set("A", null);
		result.set("B", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose("definition_of_" + name, result.getDefinition());
				
				final Node<?> nA = (Node<?>) result.get("A");
				final Node<?> nB = (Node<?>) result.get("B");
				
				final int[] lm = nA.getShape();
				final int[] mn = nB.getShape();
				
				checkArgument(lm.length == 2, "Expected length: 2 but was: " + lm.length);
				checkArgument(mn.length == 2, "Expected length: 2 but was: " + mn.length);
				
				final Object _l = $n(lm[0]);
				final Object _m = $n(lm[1]);
				final Object _n = $n(mn[1]);
				
				checkArgument(_m.equals($n(mn[0])), _m + " != " + mn[0]);
				
				final Object _A = $new("A");
				final Object _B = $new("B");
				final Object _C = $new("C");
				
				suppose($(_A, IN, $("M", "_", tuple(_l, _m))));
				suppose($(_B, IN, $("M", "_", tuple(_m, _n))));
				suppose($(_C, IN, $(R, "^", $(_l, "*", _n))));
				
				{
					subdeduction();
					
					autobindTrim("definition_of_" + name, _l, _m, _n, _A, _B, _C);
					canonicalizeLast();
					
					conclude();
				}
			}
		});
		
		return result;
	}
	
	public static final Computation innerReplicator() {
		final String name = "inner_rep";
		final Computation result = new Computation().setTypeName(name);
		
		{
			final Object _n = $new("n");
			final Object _s = $new("s");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, ",", _s, IN, POS,
								$($(name, " ", _n, " ", _s),
										"=", ptuple(
												$(p($("step_1", $(_n, "-", $(_i, "%", $($(_s, "+", 1), "*", _n))))), "_", $(_i, "<", $(_s, "*", $(_s, "*", _n)))),
												tuple(_s, $(_s, "*", _n)))))));
		}
		
		result.set("n", null);
		result.set("stride", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				final Object n = $n(result.get("n"));
				final Object s = $n(result.get("stride"));
				
				{
					subdeduction();
					
					autobindTrim(name(-1), n, s);
					canonicalizeLast();
					
					conclude();
				}
			}
		});
		
		return result;
	}
	
	public static final Computation outerReplicator() {
		final String name = "outer_rep";
		final Computation result = new Computation().setTypeName(name);
		
		{
			final Object _n = $new("n");
			final Object _s = $new("s");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, ",", _s, IN, POS,
							$($(name, " ", _n, " ", _s),
									"=", ptuple(
											$(p($("delta_", $(floor($(_i, "/", $(_s, "*", _n))), "", $($(_i, "%", $(_s, "*", _n)), "%", _s)))), "_", $(_i, "<", $(_s, "*", $(_s, "*", _n)))),
											tuple(_s, $(_s, "*", _n)))))));
		}
		
		result.set("n", null);
		result.set("stride", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				final Object n = $n(result.get("n"));
				final Object s = $n(result.get("stride"));
				
				{
					subdeduction();
					
					autobindTrim(name(-1), n, s);
					canonicalizeLast();
					
					conclude();
				}
			}
		});
		
		return result;
	}
	
	public static final Computation lowerTriangularOnes() {
		final String name = "lower_ones";
		final Computation result = new Computation().setTypeName(name);
		
		{
			final Object _n = $new("n");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, IN, POS,
							$($(name, " ", _n),
									"=", ptuple(
											$(p($("step_1", $(floor($(_i, "/", _n)), "-", $(_i, "%", _n)))), "_", $(_i, "<", $(_n, "*", _n))),
											tuple(1, $(_n, "*", _n)))))));
		}
		
		result.set("n", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				final Object n = $n(result.get("n"));
				
				{
					subdeduction();
					
					autobindTrim(name(-1), n);
					canonicalizeLast();
					
					conclude();
				}
			}
		});
		
		return result;
	}
	
	public static final Computation repeatAndIncrease() {
		final String name = "repeat_inc";
		final Computation result = new Computation().setTypeName(name);
		
		{
			final Object _n = $new("n");
			final Object _s = $new("s");
			final Object _d = $new("d");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, ",", _s, IN, POS,
							$(FORALL, _d, IN, R,
									$($(name, " ", _n, " ", _s, " ", _d),
											"=", ptuple(
													$(p($(floor($(_i, "/", _s)), "*", _d)), "_", $(_i, "<", $(_n, "*", _s))),
													tuple($(_n, "*", _s))))))));
		}
		
		result.set("n", null);
		result.set("stride", null);
		result.set("delta", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				final Object n = $n(result.get("n"));
				final Object s = $n(result.get("stride"));
				final Object d = $n(result.get("delta"));
				
				{
					subdeduction();
					
					autobindTrim(name(-1), n, s, d);
					canonicalizeLast();
					
					conclude();
				}
			}
		});
		
		return result;
	}
	
	public static final Computation range() {
		final Computation result = new Computation().setTypeName("range");
		
		{
			final Object _n = $new("n");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, IN, POS,
							$($("range", " ", _n),
									"=", ptuple(
											$(p(_i), "_", $(_i, "<", _n)),
											tuple(_n))))));
		}
		
		result.set("n", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				final Object n = $n(result.get("n"));
				
				autobindTrim(name(-1), n);
			}
		});
		
		return result;
	}
	
	public static final Computation ones() {
		final Computation result = new Computation().setTypeName("ones");
		
		{
			final Object _n = $new("n");
			final Object _s = $new("s");
			final Object _i = $new("i");
			
			result.setDefinition(
					list($(FORALL, _n, IN, POS,
							$(FORALL, _s, IN, $(POS, "^", _n),
									$($("ones", " ", _s),
											"=", ptuple(
													$(p(1), "_", $(_i, "<", $(PI, _s))),
													_s))))));
		}
		
		result.set("shape", null);
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				{
					subdeduction();
					
					final Object[] s = toObjects((int[]) result.get("shape"));
					
					autobindTrim(name(-1), $(s.length));
					
					canonicalizeForallIn(name(-1));
					
					bind(name(-1), tuple(s));
					
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
