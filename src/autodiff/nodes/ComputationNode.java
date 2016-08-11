package autodiff.nodes;

import static autodiff.reasoning.deductions.Standard.rewrite;
import static autodiff.reasoning.deductions.Standard.rewriteRight;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.proofs.Deduction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class ComputationNode extends AbstractNode<ComputationNode> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private final List<BindListener> bindListeners;
	
	private String typeName;
	
	public ComputationNode() {
		super(new ArrayList<>());
		this.bindings = new LinkedHashMap<>();
		this.definition = new ArrayList<>();
		this.bindListeners = new ArrayList<>();
	}
	
	public final List<BindListener> getBindListeners() {
		return this.bindListeners;
	}
	
	public final Map<String, Object> getBindings() {
		return this.bindings;
	}
	
	public final Object get(final String key) {
		return this.getBindings().get(key);
	}
	
	public final ComputationNode set(final String key, final Object value) {
		this.getBindListeners().forEach(l -> l.beforeBind(key, value));
		this.getBindings().put(key, value);
		this.getBindListeners().forEach(l -> l.afterBind(key, value));
		
		return this;
	}
	
	public final List<Object> getDefinition() {
		return this.definition;
	}
	
	public final ComputationNode setDefinition(final List<Object> definition) {
		this.definition = definition;
		
		return this;
	}
	
	public final String getTypeName() {
		return this.typeName;
	}
	
	public final ComputationNode setTypeName(final String typeName) {
		this.typeName = typeName;
		
		return this;
	}
	
	@Override
	public final String getName() {
		return "[" + this.getId() + "]" + this.getTypeName();
	}
	
	@Override
	public final ComputationNode autoShape() {
		Standard.build(new Deduction(AUTODIFF, this.getName() + "_type"), new Runnable() {
			
			@Override
			public final void run() {
				suppose(getDefinition());
				
				Tools.debugPrint(getDefinition());
				
				canonicalizeForallIn(name(-1));
				
				{
					subdeduction();
					
					final Object n = $(get("n"));
					
					bind(name(-1), n);
					
					deducePositivity(n);
					
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				canonicalizeForallIn(name(-1));
				
				final Object[] s = toObjects((int[]) get("s"));
				
				bind(name(-1), p(toBinaryTree(",", s)));
				
				{
					subdeduction();
					
					boolean first = true;
					
					for (final Object value : s) {
						deduceCartesianPositivity(value);
						
						if (first) {
							first = false;
						} else {
							final Object x = left(proposition(-2));
							final Object y = left(proposition(-1));
							final Object m = right(right(proposition(-2)));
							final Object n = right(right(proposition(-1)));
							
							final String type1 = name(-2);
							final String type2 = name(-1);
							
							debugPrint(m, n);
							
							{
								subdeduction();
								
								{
									subdeduction();
									
									bind("type_of_pair", (Object) $(POS, "^", m), $(POS, "^", n));
									
									canonicalizeForallIn(name(-1));
									bind(name(-1), x);
									apply(name(-1), type1);
									
									canonicalizeForallIn(name(-1));
									bind(name(-1), y);
									apply(name(-1), type2);
									
									bind("definition_of_parentheses", list(left(proposition(-1))).get(1));
									rewrite(name(-2), name(-1));
									
									conclude();
								}
								
								{
									subdeduction();
									
									canonicalizeForallIn("cartesian_m_n");
									
									bind(name(-1), POS);
									
									apply(name(-1), "positives_in_Uhm");
									
									canonicalizeForallIn2(name(-1));
									
									bind(name(-1), m);
									deducePositivity(m);
									apply(name(-2), name(-1));
									
									bind(name(-1), n);
									deducePositivity(n);
									apply(name(-2), name(-1));
									
									final Integer mn = (Integer) m + (Integer) n;
									
									verifyBasicNumericProposition($($(m, "+", n), "=", mn));
									
									rewrite(name(-2), name(-1));
									
									conclude();
								}
								
								rewrite(name(-2), name(-1));
								
								conclude();
							}
						}
					}
					
					bind("definition_of_parentheses", left(proposition(-1)));
					rewriteRight(name(-2), name(-1));
					
					conclude();
				}
				
				apply(name(-2), name(-1));
				
				// TODO
				
				abort();
			}
		}, 1);
		
		return super.autoShape();
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object U = $("℧");
	
	public static final Object IN = $("∈");
	
	public static final Object SUBSET = $("⊂");
	
	public static final Object EQUIV = $("⇔");
	
	public static final Object LAND = $("∧");
	
	public static final Object P = $("ℙ");
	
	public static final Object CROSS = $("×");

	public static final Object PI = $("Π");
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Deduction AUTODIFF = Standard.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Standard.setup();
			
			{
				final Object _X = $new("X");
				
				suppose("definition_of_parentheses", $forall(_X,
						$(p(_X), "=", _X)));
			}
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("definition_of_subset", $forall(_X, _Y,
						$($(_X, SUBSET, _Y), "=", $forall(_x, $rule($(_x, IN, _X), $(_x, IN, _Y))))));
			}
			
			{
				suppose("naturals_subset_reals",
						$(N, SUBSET, R));
			}
			
			{
				subdeduction("transitivity_of_subset");
				
				final Object _X = forall("X");
				final Object _Y = forall("Y");
				final Object _Z = forall("Z");
				
				suppose($(_X, SUBSET, _Y));
				suppose($(_Y, SUBSET, _Z));
				
				final String h1 = name(-2);
				final String h2 = name(-1);
				
				{
					subdeduction();
					
					final Object _x = forall("x");
					
					suppose($(_x, IN, _X));
					
					final String h3 = name(-1);
					
					{
						subdeduction();
						
						bind("definition_of_subset", _X, _Y);
						rewrite(h1, name(-1));
						bind(name(-1), _x);
						
						conclude();
					}
					
					apply(name(-1), h3);
					
					{
						subdeduction();
						
						bind("definition_of_subset", _Y, _Z);
						rewrite(h2, name(-1));
						bind(name(-1), _x);
						
						conclude();
					}
					
					apply(name(-1), name(-2));
					
					conclude();
				}
				
				bind("definition_of_subset", _X, _Z);
				rewriteRight(name(-2), name(-1));
				
				conclude();
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("definition_of_powerset", $forall(_X, _Y,
						$($(_X, IN, pp(_Y)), "=", $(_X, SUBSET, _Y))));
			}
			
			{
				suppose("type_of_P_R", $(pp(R), SUBSET, U));
			}
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in", $forall(_x, _X, _P,
						$($(FORALL, _x, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), _P)))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in_2", $forall(_x, _y, _X, _P,
						$($(FORALL, _x, ",", _y, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), _P)))))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in_3", $forall(_x, _y, _X, _P,
						$($(FORALL, _x, ",", _y, ",", _z, IN, _X, _P),
								"=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), $forall(_z, $rule($(_z, IN, _X), _P)))))))));
			}
			
			{
				final Object _n = $new("n");
				
				suppose("definition_of_positives", $forall(_n,
						$($(_n, IN, POS), "=", $($(_n, IN, N), LAND, $(0, "<", _n)))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("introduction_of_conjunction",
						$forall(_X, _Y,
								$rule(_X, _Y, $(_X, LAND, _Y))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("left_elimination_of_conjunction",
						$forall(_X, _Y,
								$rule($(_X, LAND, _Y), _X)));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("right_elimination_of_conjunction",
						$forall(_X, _Y,
								$rule($(_X, LAND, _Y), _Y)));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("definition_of_logical_equivalence",
						$forall(_X, _Y,
								$($(_X, EQUIV, _Y), "=", $($rule(_X, _Y), LAND, $rule(_Y, _X)))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("logical_equality",
						$forall(_X, _Y,
								$rule($rule(_X, _Y), $($rule(_Y, _X)), $(_X, "=", _Y))));
			}
			
			{
				subdeduction("logical_equivalence_implies_logical_equality");
				
				final Object _X = forall("X");
				final Object _Y = forall("Y");
				
				suppose($(_X, EQUIV, _Y));
				bind("definition_of_logical_equivalence", _X, _Y);
				rewrite(name(-2), name(-1));
				
				breakConjunction(name(-1));
				
				bind("logical_equality", _X, _Y);
				apply(name(-1), name(-3));
				apply(name(-1), name(-3));
				
				conclude();
			}
			
			{
				subdeduction("commutativity_of_conjunction");
				
				final Object _X = forall("X");
				final Object _Y = forall("Y");
				
				{
					subdeduction();
					
					suppose($(_X, LAND, _Y));
					breakConjunction(name(-1));
					
					bind("introduction_of_conjunction", _Y, _X);
					apply(name(-1), name(-2));
					apply(name(-1), name(-4));
					
					conclude();
				}
				
				{
					subdeduction();
					
					suppose($(_Y, LAND, _X));
					breakConjunction(name(-1));
					
					bind("introduction_of_conjunction", _X, _Y);
					apply(name(-1), name(-2));
					apply(name(-1), name(-4));
					
					conclude();
				}
				
				bind("logical_equality", (Object) $(_X, LAND, _Y), $(_Y, LAND, _X));
				apply(name(-1), name(-3));
				apply(name(-1), name(-3));
				
				conclude();
			}
			
			{
				subdeduction("positives_subset_naturals");
				
				bind("definition_of_subset", POS, N);
				
				{
					subdeduction();
					
					final Object _x = forall("y");
					
					suppose($(_x, IN, POS));
					bind("definition_of_positives", _x);
					rewrite(name(-2), name(-1));
					deduceConjunctionLeft(name(-1));
					
					conclude();
				}
				
				rewriteRight(name(-1), name(-2));
				
				conclude();
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				
				suppose("definition_of_M_s",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n,
										$($("M", "_", _s), "=", $($(R, "^", $(PI, _s)), CROSS, c(_s)))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _X = $new("X");
				final Object _i = $new("i");
				final Object _j = $new("j");
				
				suppose("type_of_flat",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n,
										$forall(_X, $($("flat", " ", $(p(1), "_", $(_i, IN, cartesian(_s, _j, _n)))), IN, $(R, "^", $(PI, _s))))))));
			}
			
			{
				final Object _X = $new("X");
				
				suppose("definition_of_singleton",
						$forall(_X,
								$(_X, IN, c(_X))));
			}
			
			{
				final Object _X = $new("X");
				final Object _x = $new("x");
				
				suppose("type_of_single",
						$forall(_X,
								$(FORALL, _x, IN, _X,
												$(p(_x), IN, _X))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("type_of_pair",
						$forall(_X, _Y,
								$(FORALL, _x, IN, _X,
										$(FORALL, _y, IN, _Y,
												$(p(_x, ",", _y), IN, $(_X, CROSS, _Y))))));
			}
			
			{
				final Object _X = $new("X");
				
				suppose("cartesian_1",
						$(FORALL, _X, IN, U,
								$(_X, "=", $(_X, "^", 1))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("type_of_cartesian",
						$(FORALL, _X, ",", _Y, IN, U,
								$(pp(_X, CROSS, _Y), SUBSET, U)));
			}
			
			{
				final Object _X = $new("X");
				final Object _m = $new("m");
				final Object _n = $new("n");
				
				suppose("cartesian_m_n",
						$(FORALL, _X, IN, U,
								$(FORALL, _m, ",", _n, IN, POS,
										$($($(_X, "^", _m), CROSS, $(_X, "^", _n)), "=", $(_X, "^", $(_m, "+", _n))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _Z = $new("Z");
				
				suppose("cartesian_associativity",
						$(FORALL, _X, ",", _Y, ",", _Z, IN, U,
										$($(p(_X, CROSS, _Y), CROSS, _Z), "=", $(_X, CROSS, p(_Y, CROSS, _Z)))));
			}
			
			deducePositivesInUhm();
		}
		
	}, 1);
	
	public static final void deducePositivesInUhm() {
		subdeduction("positives_in_Uhm");
		
		{
			subdeduction();
			
			bind("transitivity_of_subset", POS, N, R);
			apply(name(-1), "positives_subset_naturals");
			apply(name(-1), "naturals_subset_reals");
			
			conclude();
		}
		
		bind("definition_of_powerset", POS, R);
		rewriteRight(name(-2), name(-1));
		
		{
			subdeduction();
			
			bind("definition_of_subset", pp(R), U);
			rewrite("type_of_P_R", name(-1));
			bind(name(-1), POS);
			
			conclude();
		}
		
		apply(name(-1), name(-2));
		
		conclude();
	}
	
	public static final ComputationNode ones() {
		final ComputationNode result = new ComputationNode().setTypeName("ones");
		
		final Object n = $new("n");
		final Object s = $new("s");
		final Object i = $new("i");
		
		result.setDefinition(
				$(FORALL, n, IN, POS,
						$(FORALL, s, IN, $(POS, "^", n),
								$($("ones", " ", s), "=", p($(p(1), "_", $(i, "<", $(PI, s))), ",", s)))));
		
		result.set("s", null);
		
		result.getBindListeners().add(new BindListener() {
			
			@Override
			public final void beforeBind(final String key, final Object value) {
				if ("s".equals(key)) {
					final int[] shape = (int[]) value;
					
					NodesTools.check(0 < shape.length, () -> "Invalid shape: []");
					
					result.set("n", shape.length);
				}
			}
			
			private static final long serialVersionUID = -64734290035563118L;
			
		});
		
		debugPrint(deepJoin(" ", result.getDefinition()));
		debugPrint(result.getBindings().keySet());
		
		return result;
	}
	
	public static final Integer[] toObjects(final int... values) {
		final Integer[] result = new Integer[values.length];
		
		for (int i = 0; i < values.length; ++i) {
			result[i] = values[i];
		}
		
		return result;
	}
	
	public static final Object toBinaryTree(final String operator, final Object... objects) {
		final int n = objects.length;
		
		if (n == 0) {
			return $();
		}
		
		Object result = $(objects[0]);
		
		for (int i = 1; i < n; ++i) {
			result = $(result, operator, objects[i]);
		}
		
		return result;
	}
	
	public static final List<Object> p(final Object... objects) {
		return $("(", $(objects), ")");
	}
	
	public static final List<Object> c(final Object... objects) {
		return $("{", $(objects), "}");
	}
	
	public static final void deducePositivity(final Object target) {
		subdeduction();
		
		bind("definition_of_positives", target);
		
		{
			subdeduction();
			
			verifyBasicNumericProposition($(target, IN, N));
			verifyBasicNumericProposition($(0, "<", target));
			
			bind("introduction_of_conjunction", proposition(-2), proposition(-1));
			apply(name(-1), name(-3));
			apply(name(-1), name(-3));
			
			conclude();
		}
		
		rewriteRight(name(-1), name(-2));
		
		conclude();
	}
	
	public static final void deduceCartesianPositivity(final Object value) {
		subdeduction();
		
		deducePositivity(value);
		
		{
			subdeduction();
			
			canonicalizeForallIn("cartesian_1");
			bind(name(-1), POS);
			apply(name(-1), "positives_in_Uhm");
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn(final String targetName) {
		final Object proposition = proposition(targetName);
		
		subdeduction();
		
		bind("definition_of_forall_in", list(proposition).get(1), list(proposition).get(3), list(proposition).get(4));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn2(final String targetName) {
		final Object proposition = proposition(targetName);
		
		subdeduction();
		
		bind("definition_of_forall_in_2", list(proposition).get(1), list(proposition).get(3), list(proposition).get(5), list(proposition).get(6));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final String deepJoin(final String separator, final Iterable<?> objects) {
		final StringBuilder resultBuilder = new StringBuilder();
		boolean first = true;
		
		for (final Object object : objects) {
			final Iterable<?> subobjects = cast(Iterable.class, object);
			
			if (first) {
				first = false;
			} else {
				resultBuilder.append(separator);
			}
			
			resultBuilder.append(subobjects == null ? object : deepJoin(separator, subobjects));
		}
		
		return resultBuilder.toString();
	}
	
	public static final Object cartesian(final Object _s, final Object _j, final Object _n) {
		return $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j))));
	}
	
	public static final Object pp(final Object... set) {
		return $(P, p(set));
	}
	
	public static final void breakConjunction(final String targetName) {
		deduceConjunctionLeft(targetName);
		deduceConjunctionRight(targetName);
	}
	
	public static final void deduceConjunctionLeft(final String targetName) {
		final Object proposition = proposition(targetName);
		final Object left = left(proposition);
		final Object right = right(proposition);
		
		subdeduction();
		
		bind("left_elimination_of_conjunction", left, right);
		apply(name(-1), targetName);
		
		conclude();
	}
	
	public static final void deduceConjunctionRight(final String targetName) {
		final Object proposition = proposition(targetName);
		final Object left = left(proposition);
		final Object right = right(proposition);
		
		subdeduction();
		
		bind("right_elimination_of_conjunction", left, right);
		apply(name(-1), targetName);
		
		conclude();
	}
	
	/**
	 * @author codistmonk (creation 2016-08-10)
	 */
	public static abstract interface BindListener extends Serializable {
		
		public default void beforeBind(final String key, final Object value) {
			// NOP
		}
		
		public default void afterBind(final String key, final Object value) {
			// NOP
		}
		
	}
	
}
