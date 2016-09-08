package autodiff.nodes;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Propositions.*;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalize;
import static autodiff.reasoning.deductions.ScalarAlgebra.newElementarySimplificationRule;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.rules.Variable.matchOrFail;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.ScalarAlgebra;
import autodiff.reasoning.deductions.ToCLCode;
import autodiff.reasoning.deductions.ToJavaCode;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Auto.Simplifier;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.rules.Rules;
import multij.rules.TryRule;
import multij.rules.Variable;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class Computation extends AbstractNode<Computation> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private final List<BindListener> bindListeners;
	
	private String typeName;
	
	private Runnable binder;
	
	private Deduction boundForm;
	
	public Computation() {
		super(new ArrayList<>());
		this.bindings = new LinkedHashMap<>();
		this.definition = new ArrayList<>();
		this.bindListeners = new ArrayList<>();
	}
	
	@Override
	public final boolean isComputationNode() {
		return true;
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
	
	public final Computation set(final String key, final Object value) {
		this.getBindListeners().forEach(l -> l.beforeBind(key, value));
		this.getBindings().put(key, value);
		this.getBindListeners().forEach(l -> l.afterBind(key, value));
		
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
		final Object shapeExpression = right(middle(right(proposition)));
		
		setShape(toInts(flattenSequence(",", shapeExpression)));
		
		return this;
	}
	
	public final Deduction getBoundForm() {
		if (this.boundForm == null) {
			this.boundForm = Basics.build(new Deduction(
					AUTODIFF, this.getName() + "_bind"), this.getBinder(), new Simple(1));
		}
		
		return this.boundForm;
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object PI = $("Π");
	
	public static final Deduction AUTODIFF = Basics.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			ScalarAlgebra.load();
			
			supposeEliminationOfParentheses();
			
			supposeTypeOfPowersetOfReals();
			
			supposeDefinitionOfRange();
			
			deducePositivesSubsetNaturals();
			deducePositivesInUhm();
			supposeDefinitionOfMs();
			supposeTypeOfFlat();
			supposeDefinitionOfSingleton();
			
			supposeDefinitionOfProductLoop0();
			supposeDefinitionOfProductLoopN();
			supposeDefinitionOfProductReduction();
			
			{
				suppose("positives_single_in_Uhm",
						$($1(POS), IN, U));
			}
			
			supposeDefinitionOfVectorReductionByProduct();
			testVectorReductionByProduct();
			
			for (final Object type : array(R, N)) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_addition_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$($(_x, "+", _y), IN, type)));
			}
			
			for (final Map.Entry<Object, Object> entry : map("addition", $("+"), "multiplication", $("*")).entrySet()) {
				{
					final Object _x = $new("x");
					final Object _y = $new("y");
					final Object op = entry.getValue();
					
					suppose("commutativity_of_" + entry.getKey(),
							$(FORALL, _x, ",", _y, IN, R,
									$($(_x, op, _y), "=", $(_y, op, _x))));
				}
				
				{
					final Object _x = $new("x");
					final Object _y = $new("y");
					final Object _z = $new("z");
					final Object op = entry.getValue();
					
					suppose("associativity_of_" + entry.getKey(),
							$(FORALL, _x, ",", _y, ",", _z, IN, R,
									$($($(_x, op, _y), op, _z), "=", $(_x, op, $(_y, op, _z)))));
				}
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("definition_of_subtraction",
						$(FORALL, _x, ",", _y, IN, R,
								$($(_x, "-", _y), "=", $(_x, "+", $(-1, "*", _y)))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("associativity_of_+-",
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$($($(_x, "+", _y), "-", _z), "=", $(_x, "+", $(_y, "-", _z)))));
			}
			
			{
				suppose("relatives_in_Uhm",
						$(Z, IN, U));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("subtraction_in_naturals",
						$(FORALL, _x, ",", _y, IN, Z,
								$rule($(_y, LE, _x), $($(_x, "-", _y), IN, N))));
			}
			
			ToJavaCode.load();
			ToCLCode.load();
		}
		
	}, new Simple(1));
	
	public static final void computeVectorReductionByProduct(final Object formula) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			rules.add(rule($(PI, $()),
					(_1, m) -> {
						// NOP
						
						return null;
					}));
		}
		
		{
			final Variable _x0 = v("x0");
			
			rules.add(rule($(PI, $1(_x0)),
					(_1, m) -> {
						autobindTrim("definition_of_vector_reduction_by_product_1",
								m.get(_x0));
						
						return null;
					}));
		}
		
		{
			final Variable _s = v("s");
			final Variable _x0 = v("x0");
			final Variable _x1 = v("x1");
			
			rules.add(rule($(PI, $(_x0, $(_s, _x1))),
					(_1, m) -> {
						{
							subdeduction();
							
							autobindTrim("definition_of_vector_reduction_by_product_2",
									m.get(_s), m.get(_x0), m.get(_x1));
							
							simplifyElementaryExpression(name(-1), right(proposition(-1)));
							
							conclude();
						}
						
						return null;
					}));
		}
		
		{
			final Variable _s = v("s");
			final Variable _x0 = v("x0");
			final Variable _x1 = v("x1");
			final Variable _x2 = v("x2");
			
			rules.add(rule($(PI, $(_x0, $(_s, _x1, _x2))),
					(_1, m) -> {
						{
							subdeduction();
							
							autobindTrim("definition_of_vector_reduction_by_product_3",
									m.get(_s), m.get(_x2), m.get(_x0), m.get(_x1));
							
							computeVectorReductionByProduct(right(right(proposition(-1))));
							
							rewrite(name(-2), name(-1));
							
							simplifyElementaryExpression(name(-1), right(proposition(-1)));
							
							conclude();
						}
						
						return null;
					}));
		}
		
		rules.applyTo(formula);
	}
	
	public static final Computation ones() {
		final Computation result = new Computation().setTypeName("ones");
		
		final Object n = $new("n");
		final Object s = $new("s");
		final Object i = $new("i");
		
		result.setDefinition(
				list($(FORALL, n, IN, POS,
						$(FORALL, s, IN, $(POS, "^", n),
								$($("ones", " ", s), "=", p($(p(1), "_", $(i, "<", $(PI, s))), ",", s))))));
		
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
		
		result.setBinder(new Runnable() {
			
			@Override
			public final void run() {
				suppose(result.getDefinition());
				
				{
					subdeduction();
					
					final Object[] s = toObjects((int[]) result.get("s"));
					
					autobindTrim(name(-1), $(result.get("n")));
					
					canonicalizeForallIn(name(-1));
					
					bind(name(-1), sequence(",", s));
					
					deduceCartesianProduct(POS, s);
					
					apply(name(-2), name(-1));
					
					final Object valuesExpression = left(middle(right(proposition(-1))));
					final Object nExpression = right(right(valuesExpression));
					
					{
						subdeduction();
						
						computeVectorReductionByProduct(nExpression);
						rewrite(name(-2), name(-1));
						
						conclude();
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
	
	public static final List<Object> flattenBinaryTree(final Object binaryTree) {
		return new FlattenBinaryTree().apply(binaryTree);
	}
	
	public static final Object cartesian(final Object _s, final Object _j, final Object _n) {
		return $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j))));
	}
	
	public static final void supposeEliminationOfParentheses() {
		final Object _X = $new("X");
		
		suppose("elimination_of_parentheses", $forall(_X,
				$(p(_X), "=", _X)));
	}
	
	public static final void supposeTypeOfPowersetOfReals() {
		suppose("type_of_P_R",
				$(pp(R), SUBSET, U));
	}
	
	public static final void deducePositivesSubsetNaturals() {
		subdeduction("positives_subset_naturals");
		
		autobindTrim("definition_of_subset", POS, N);
		
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
	
	public static final void supposeDefinitionOfMs() {
		final Object _n = $new("n");
		final Object _s = $new("s");
		
		suppose("definition_of_M_s",
				$(FORALL, _n, IN, POS,
						$(FORALL, _s, IN, $(POS, "^", _n,
								$($("M", "_", _s), "=", $($(R, "^", $(PI, _s)), CROSS, c(_s)))))));
	}
	
	public static final void supposeTypeOfFlat() {
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
	
	public static final void deducePositivesInUhm() {
		subdeduction("positives_in_Uhm");
		
		autobindTrim("subset_in_Uhm", POS, N);
		
		conclude();
	}
	
	public static final void supposeDefinitionOfProductLoop0() {
		final Object _X = $new("X");
		final Object _i = $new("i");
		
		suppose("definition_of_product_loop_0",
				$forall(_i, _X,
						$($(PI, "_", $(_i, "<", 0), _X), "=", 1)));
	}
	
	public static final void supposeDefinitionOfProductLoopN() {
		final Object _n = $new("n");
		final Object _X = $new("X");
		final Object _i = $new("i");
		
		suppose("definition_of_product_loop_n",
				$(FORALL, _n, IN, POS,
						$forall(_i, _X,
								$rule($rule($(_i, IN, $(N, "_", $("<", _n))), $(_X, IN, R)),
										$($(PI, "_", $(_i, "<", _n), _X),
												"=", $($(PI, "_", $(_i, "<", $(_n, "-", 1)), _X), "*", $(_X, "|", $1($replacement(_i, $(_n, "-", 1))), "@", $())))))));
	}
	
	public static final void supposeDefinitionOfProductReduction() {
		final Object _n = $new("n");
		final Object _v = $new("v");
		final Object _i = $new("i");
		
		suppose("definition_of_product_reduction",
				$(FORALL, _n, IN, POS,
						$(FORALL, _v, IN, $(R, "^", _n),
								$($(PI, _v), "=", $(PI, "_", $(_i, "<", _n), $(_v, "_", _i))))));
	}
	
	public static final void supposeDefinitionOfVectorReductionByProduct() {
		{
			suppose("definition_of_vector_reduction_by_product_0",
					$($(PI, $()), "=", 1));
		}
		
		{
			final Object _x0 = $new("x0");
			
			suppose("definition_of_vector_reduction_by_product_1",
					$(FORALL, _x0, IN, R,
							$($(PI, $1(_x0)), "=", _x0)));
		}
		
		{
			final Object _s = $new("s");
			final Object _x0 = $new("x0");
			final Object _x1 = $new("x1");
			
			suppose("definition_of_vector_reduction_by_product_2",
					$forall(_s,
							$(FORALL, _x0, ",", _x1, IN, R,
									$($(PI, $(_x0, $(_s, _x1))), "=", $(_x0, "*", _x1)))));
		}
		
		{
			final Object _s = $new("s");
			final Object _x0 = $new("x0");
			final Object _x1 = $new("x1");
			final Object _x2 = $new("x2");
			
			suppose("definition_of_vector_reduction_by_product_3",
					$forall(_s, _x2,
							$(FORALL, _x0, ",", _x1, IN, R,
									$($(PI, $(_x0, $(_s, _x1, _x2))), "=", $(_x0, "*", $(PI, $(_x1, _x2)))))));
		}
	}
	
	public static final void testVectorReductionByProduct() {
		subdeduction("vector_reduction_by_product.test1");
		
		computeVectorReductionByProduct($(PI, sequence(",", 1, 2, 3)));
		
		conclude();
	}
	
	public static final void sequenceUnappendInLast(final Object separator) {
		new Simplifier(Simplifier.Mode.DEFINE)
		.add(newSequenceUnappendRule(separator))
		.apply(right(proposition(-1)));
	}
	
	public static final void commuteEquality(final String targetName) {
		final Object target = proposition(targetName);
		
		autobindTrim("commutativity_of_equality", left(target), right(target));
	}
	
	public static final void leftEliminateDisjunction(final String targetName) {
		final Variable vx = v("x");
		final Variable vy = v("y");
		final Variable vz = v("z");
		
		matchOrFail($rule($(vx, LOR, vy), vz), proposition(targetName));
		
		autobindTrim("left_elimination_of_disjunction", vx.get(), vy.get(), vz.get());
	}
	
	public static final void rightEliminateDisjunction(final String targetName) {
		final Variable vx = v("x");
		final Variable vy = v("y");
		final Variable vz = v("z");
		
		matchOrFail($rule($(vx, LOR, vy), vz), proposition(targetName));
		
		autobindTrim("right_elimination_of_disjunction", vx.get(), vy.get(), vz.get());
	}
	
	public static final void canonicalizeLast() {
		subdeduction();
		
		canonicalize(proposition(-1));
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void subsituteLast() {
		final Variable vX = v("X");
		final Variable ve = v("e");
		
		matchOrFail($(vX, "|", ve, "@", $()), proposition(-1));
		
		subdeduction();
		
		substitute(vX.get(), toMap(ve.get()));
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void simplifySubstitutionsAndForallInsAndElementary(final Object expression, final Simplifier.Mode mode) {
		new Simplifier(mode)
		.add(newElementarySimplificationRule())
		.add(newSubstitutionSimplificationRule())
		.add(newForallInSimplificationRule())
		.add(newForallIn2SimplificationRule())
		.add(newForallIn3SimplificationRule())
		.add(tryMatch(new Variable("*"), (e, m) -> false))
		.simplifyCompletely(expression);
	}
	
	public static final void simplifySubstitutionsAndElementaryInLast() {
		simplifySubstitutionsAndElementaryInLast(Simplifier.Mode.DEFINE);
	}
	
	public static final void simplifySubstitutionsAndElementaryInLast(final Simplifier.Mode mode) {
		new Simplifier(mode)
				.add(newElementarySimplificationRule())
				.add(newSubstitutionSimplificationRule())
				.add(tryMatch(new Variable("*"), (e, m) -> false))
				.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceAppendAndConcatenateInLast() {
		new Simplifier()
		.add(newSequenceAppendSimplificationRule())
		.add(newSequenceConcatenateSimplificationRule())
		.add(tryMatch(new Variable("*"), (e, m) -> false))
		.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceAppendInLast() {
		new Simplifier()
				.add(newSequenceAppendSimplificationRule())
				.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceConcatenateInLast() {
		new Simplifier()
				.add(newSequenceConcatenateSimplificationRule())
				.simplifyCompletely(proposition(-1));
	}
	
	public static final TryRule<Object> newSequenceUnappendRule(final Object separator) {
		return tryMatch(new Variable("*"), (e, m) -> {
			final List<Object> s = flattenSequence(separator, e);
			
			if (s.isEmpty()) {
				return false;
			}
			
			final int n = s.size();
			final List<Object> prefix = sequence(separator, s.subList(0, n - 1).toArray());
			
			subdeduction();
			
			if (1 == n) {
				autobindTrim("definition_of_sequence_append_0",
						separator, prefix, last(s));
			} else if (2 == n) {
				autobindTrim("definition_of_sequence_append_1",
						separator, prefix, first(prefix), last(s));
			} else {
				autobindTrim("definition_of_sequence_append_2",
						separator, prefix, first(prefix), second(prefix), last(s));
				
				new Simplifier(Mode.DEFINE)
				.add(newSequenceSubappendSimplificationRule())
				.simplifyCompletely(proposition(-1));
			}
			
			autobindTrim("commutativity_of_equality",
					left(proposition(-1)), right(proposition(-1)));
			
			conclude();
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSequenceAppendSimplificationRule() {
		final Variable vs = v("s");
		final Variable vx = v("x");
		final Variable vy = v("y");
		
		return tryMatch($("sequence_append", vs, vx, vy), (e, m) -> {
			computeSequenceAppend(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSequenceSubappendSimplificationRule() {
		final Variable vs = v("s");
		final Variable vx = v("x");
		final Variable vy = v("y");
		
		return tryMatch($("sequence_subappend", vs, vx, vy), (e, m) -> {
			computeSequenceSubappend(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSequenceConcatenateSimplificationRule() {
		final Variable vs = v("s");
		final Variable vx = v("x");
		final Variable vy = v("y");
		
		return tryMatch($("sequence_concatenate", vs, vx, vy), (e, m) -> {
			computeSequenceConcatenate(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSubstitutionSimplificationRule() {
		final Variable vx = v("x");
		final Variable ve = v("e");
		final Variable vi = v("i");
		
		return tryMatch($(vx, "|", ve, "@", vi), (e, m) -> {
			substitute(vx.get(), toMap(ve.get()), toInts(vi.get()));
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallInSimplificationRule() {
		final Variable vx = v("x");
		final Variable vX = v("X");
		final Variable vP = v("P");
		
		return tryMatch($(FORALL, vx, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in", vx.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallIn2SimplificationRule() {
		final Variable vx = v("x");
		final Variable vy = v("y");
		final Variable vX = v("X");
		final Variable vP = v("P");
		
		return tryMatch($(FORALL, vx, ",", vy, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in_2", vx.get(), vy.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallIn3SimplificationRule() {
		final Variable vx = v("x");
		final Variable vy = v("y");
		final Variable vz = v("z");
		final Variable vX = v("X");
		final Variable vP = v("P");
		
		return tryMatch($(FORALL, vx, ",", vy, ",", vz, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in_3", vx.get(), vy.get(), vz.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final int[] toInts(final Object indices) {
		return list(indices).stream().mapToInt(i -> ((Number) i).intValue()).toArray(); 
	}
	
	public static final Map<Object, Object> toMap(final Object replacements) {
		final Map<Object, Object> result = new LinkedHashMap<>();
		
		for (final Object equality : list(replacements)) {
			result.put(left(equality), right(equality));
		}
		
		return result;
	}
	
	public static final void supposeDefinitionOfRange() {
		final Object _i = $new("i");
		final Object _n = $new("n");
		
		suppose("definition_of_range",
				$(FORALL, _n, IN, N,
						$forall(_i,
								$($(_i, IN, $(N, "_", $("<", _n))),
										"=", $($(_i, IN, N), LAND, $(_i, "<", _n))))));
	}
	
	public static final int[] toInts(final List<Object> numbers) {
		return numbers.stream().mapToInt(n -> ((Number) n).intValue()).toArray();
	}
	
	/**
	 * @author codistmonk (creation 2016-08-10)
	 */
	public static abstract interface BindListener extends Serializable {
		
		public default void beforeBind(final String key, final Object value) {
			ignore(key);
			ignore(value);
		}
		
		public default void afterBind(final String key, final Object value) {
			ignore(key);
			ignore(value);
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-15)
	 */
	public static final class RepeatHelper implements Serializable {
		
		private final Object s;
		
		private final Object x;
		
		private final int n;
		
		public RepeatHelper(final Object s, final Object x, final int n) {
			this.s = s;
			this.x = x;
			this.n = n;
			
			if (n < 0) {
				throw new IllegalArgumentException();
			}
		}
		
		public final void compute() {
			if (this.n == 0) {
				autobind("definition_of_repeat_0", this.s, this.x);
			} else {
				subdeduction();
				
				{
					subdeduction();
					
					autobindTrim("definition_of_repeat_n", this.s, this.x, this.n);
					verifyElementaryProposition($($(this.n, "-", 1), "=", this.n - 1));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				new RepeatHelper(this.s, this.x, this.n - 1).compute();
				rewrite(name(-2), name(-1));
				
				final List<?> formula = list(right(proposition(-1)));
				
				computeSequenceAppend(this.s, formula.get(2), formula.get(3));
				rewrite(name(-2), name(-1));
				
				conclude();
			}
		}
		
		private static final long serialVersionUID = -3837963189941891310L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-11)
	 */
	public static final class FlattenBinaryTree implements ExpressionVisitor<List<Object>> {
		
		private final List<Object> result = new ArrayList<>();
		
		@Override
		public final List<Object> visit(final Object expression) {
			this.getResult().add(expression);
			
			return this.getResult();
		}
		
		@Override
		public final List<Object> visit(final List<?> expression) {
			this.apply(left(expression));
			this.apply(right(expression));
			
			return this.getResult();
		}
		
		public final List<Object> getResult() {
			return this.result;
		}
		
		private static final long serialVersionUID = 9145572614566666571L;
		
	}
	
}
