package autodiff.nodes;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Propositions.*;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.rules.Variable.match;
import static autodiff.rules.Variable.matchOrFail;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.Propositions;
import autodiff.reasoning.deductions.Sequences;
import autodiff.reasoning.deductions.Sets;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Substitution;
import autodiff.rules.Rule;
import autodiff.rules.Rules;
import autodiff.rules.SimpleRule;
import autodiff.rules.Variable;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Pair;

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
//		final Object shapeExpression = middle(right(middle(right(proposition))));
		final Object shapeExpression = right(middle(right(proposition)));
		
		setShape(toInts(flattenSequence(",", shapeExpression)));
		
		return this;
	}
	
	public final Deduction getBoundForm() {
		if (this.boundForm == null) {
			this.boundForm = Basics.build(new Deduction(
					AUTODIFF, this.getName() + "_bind"), this.getBinder(), 1);
		}
		
		return this.boundForm;
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object PI = $("Π");
	
	public static final Deduction AUTODIFF = Basics.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Basics.setup();
			Sequences.setup();
			Sets.setup();
			Propositions.setup();
			
			supposeEliminationOfParentheses();
			
			supposeTypeOfPowersetOfReals();
			supposeRealsInUhm();
			supposeNaturalsSubsetReals();
			deduceNaturalsInUhm();
			supposeDefinitionOfPositives();
			
			supposeDefinitionOfRange();
			
			deduceTransitivityOfSubset();
			deducePositivesSubsetNaturals();
			deducePositivesInUhm();
			supposeDefinitionOfMs();
			supposeTypeOfFlat();
			supposeDefinitionOfSingleton();
			
			supposeVectorTypeInUhm();
			
			supposeTypeOfSingle();
			supposeTypeOfSingleInUhm();
			
			supposeTypeOfTuple();
			supposeTypeOfTupleInUhm();
			
			{
				subdeduction("single_N_in_Uhm");
				
				ebindTrim("type_of_single_in_Uhm", N);
				
				conclude();
			}
			
			testTypeOfTuple();
			
			supposeDefinitionsForRepeat();
			
			supposeSimplificationOfTypeOfTuple();
			testSimplificationOfTypeOfTuple();
			
			supposeDefinitionOfProductLoop0();
			supposeDefinitionOfProductLoopN();
			supposeDefinitionOfProductReduction();
			
			{
				suppose("positives_single_in_Uhm",
						$($1(POS), IN, U));
			}
			
			{
				suppose("reals_single_in_Uhm",
						$($1(R), IN, U));
			}
			
			supposeDefinitionsForVectorAccess();
			testVectorAccess();
			
			supposeDefinitionOfVectorReductionByProduct();
			testVectorReductionByProduct();
			
			for (final Object type : array(R, N)) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_addition_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$($(_x, "+", _y), IN, type)));
			}
			
			for (final Object operator : array($("<"), $("<="), LE, ">", ">=", GE)) {
				{
					final Object _x = $new("x");
					final Object _y = $new("y");
					final Object _z = $new("z");
					
					suppose("transitivity_of_" + operator,
							$(FORALL, _x, ",", _y, ",", _z, IN, R,
									$rule($(_x, operator, _y), $(_y, operator, _z), $(_x, operator, _z))));
				}
				
				{
					final Object _x = $new("x");
					final Object _y = $new("y");
					final Object _z = $new("z");
					
					suppose("preservation_of_" + operator + "_under_addition",
							$(FORALL, _x, ",", _y, ",", _z, IN, R,
									$rule($(_x, operator, _y), $($(_x, "+", _z), operator, $(_y, "+", _z)))));
				}
			}
			
			for (final Object operator : array($("<"), $("<="), LE)) {
				{
					final Object _x = $new("x");
					final Object _y = $new("y");
					
					suppose("preservation_of_" + operator + "_under_multiplication",
							$(FORALL, _x, ",", _y, IN, R,
									$rule($(0, operator, _x), $(0, operator, _y), $(0, operator, $(_x, "*", _y)))));
				}
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("transitivity_of_" + LE + "<",
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$rule($(_x, LE, _y), $(_y, "<", _z), $(_x, "<", _z))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("transitivity_of_<" + LE,
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$rule($(_x, "<", _y), $(_y, LE, _z), $(_x, "<", _z))));
			}
			
			for (final Object operator : array("<", ">")) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose(operator + "_implies_not_equal",
						$(FORALL, _x, ",", _y, IN, R,
								$rule($(_x, operator, _y), $(LNOT, $(_x, "=", _y)))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("conversion<>",
						$(FORALL, _x, ",", _y, IN, R,
								$($(_x, "<", _y), "=", $(_y, ">", _x))));
			}
			
			{
				final Object _x = $new("x");
				
				suppose("neutrality_of_0",
						$(FORALL, _x, IN, R,
								$($(_x, "+", 0), "=", _x)));
			}
			
			{
				final Object _x = $new("x");
				
				suppose("neutrality_of_1",
						$(FORALL, _x, IN, R,
								$($(_x, "*", 1), "=", _x)));
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
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("equality_<" + LE,
						$(FORALL, _x, ",", _y, IN, Z,
								$($(_x, "<", _y), "=", $($(_x, "+", 1), LE, _y))));
			}
			
			{
				final Object _x = $new("x");
				
				suppose("nonnegativity_of_naturals",
						$(FORALL, _x, IN, N,
								$(0, LE, _x)));
			}
			
			{
				suppose("naturals_subset_relatives",
						$(N, SUBSET, Z));
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
			
			supposeDefinitionsForJavaCode();
			supposeDefinitionsForCLCode();
		}
		
	}, 1);
	
	public static final Object instructions(final Object instructionsBefore, final Object... newInstructions) {
		Object result = instructionsBefore;
		
		for (final Object instruction : newInstructions) {
			result = $("sequence_append", ";", result, instruction);
		}
		
		return result;
	}
	
	public static final Object block(final Object... arguments) {
		return $("()->{", sequence(";", arguments), "}");
	}
	
	public static final Object app(final Object name, final Object... arguments) {
		return $(name, "(", sequence(",", arguments), ")");
	}
	
	public static final Object str(final Object object) {
		return $("\"", object, "\"");
	}
	
	public static final int sequenceLength(final Object separator, final Object sequence) {
		final List<?> list = list(sequence);
		
		if (list.size() <= 1) {
			return list.size();
		}
		
		final List<?> second = list(second(sequence));
		
		if (2 == second.size() && separator.equals(first(second))) {
			return 2;
		}
		
		if (3 == second.size() && separator.equals(first(second))) {
			return 1 + sequenceLength(separator, $(second(second), third(second)));
		}
		
		throw new IllegalArgumentException();
	}
	
	public static final void computeVectorAccess(final Object elementType, final Object formula) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final Variable _x = new Variable("x");
			
			rules.add(rule($(_x, "_", 0), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_vector_access_0", elementType, sequenceLength(",", m.get(_x)), m.get(_x));
					computeSequenceHead(m.get(_x));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			final Variable _x = new Variable("x");
			final Variable _i = new Variable("i");
			
			rules.add(rule($(_x, "_", _i), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_vector_access_i", elementType, sequenceLength(",", m.get(_x)), m.get(_i), m.get(_x));
					simplifyElementaryExpression(name(-1), right(right(proposition(-1))));
					
					computeSequenceTail(",", m.get(_x));
					rewrite(name(-2), name(-1));
					
					computeVectorAccess(elementType, right(proposition(-1)));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		rules.applyTo(formula);
	}
	
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
			final Variable _x0 = new Variable("x0");
			
			rules.add(rule($(PI, $1(_x0)),
					(_1, m) -> {
						ebindTrim("definition_of_vector_reduction_by_product_1",
								m.get(_x0));
						
						return null;
					}));
		}
		
		{
			final Variable _s = new Variable("s");
			final Variable _x0 = new Variable("x0");
			final Variable _x1 = new Variable("x1");
			
			rules.add(rule($(PI, $(_x0, $(_s, _x1))),
					(_1, m) -> {
						{
							subdeduction();
							
							ebindTrim("definition_of_vector_reduction_by_product_2",
									m.get(_s), m.get(_x0), m.get(_x1));
							
							simplifyElementaryExpression(name(-1), right(proposition(-1)));
							
							conclude();
						}
						
						return null;
					}));
		}
		
		{
			final Variable _s = new Variable("s");
			final Variable _x0 = new Variable("x0");
			final Variable _x1 = new Variable("x1");
			final Variable _x2 = new Variable("x2");
			
			rules.add(rule($(PI, $(_x0, $(_s, _x1, _x2))),
					(_1, m) -> {
						{
							subdeduction();
							
							ebindTrim("definition_of_vector_reduction_by_product_3",
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
	
	public static final List<Pair<String, Map<Variable, Object>>> findConclusions(final Object pattern) {
		final List<Pair<String, Map<Variable, Object>>> result = new ArrayList<>();
		
		for (final PropositionDescription description : iterateBackward(deduction())) {
			final LinkedHashMap<Variable, Object> mapping = new LinkedHashMap<>();
			
			if (Variable.match(pattern, eultimate(description.getProposition()), mapping)) {
				result.add(new Pair<>(description.getName(), mapping));
			}
		}
		
		Collections.reverse(result);
		
		return result;
	}
	
	public static final Object eultimate(final Object expression) {
		if (isForallIn(expression) || isForallIn2(expression)) {
			return eultimate(last(list(expression)));
		}
		
		if (isBlock(expression)) {
			return eultimate(scope(expression));
		}
		
		if (isRule(expression)) {
			return eultimate(conclusion(expression));
		}
		
		return expression;
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
					
					ebindTrim(name(-1), $(result.get("n")));
					
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
	
	public static final void supposeEliminationOfParentheses() {
		final Object _X = $new("X");
		
		suppose("elimination_of_parentheses", $forall(_X,
				$(p(_X), "=", _X)));
	}
	
	public static final void supposeNaturalsSubsetReals() {
		suppose("naturals_subset_reals",
				$(N, SUBSET, R));
	}
	
	public static final void deduceTransitivityOfSubset() {
		subdeduction("transitivity_of_subset");
		
		final Object _X = forall("X");
		final Object _Y = forall("Y");
		final Object _Z = forall("Z");
		
		suppose($(_X, IN, U));
		suppose($(_Y, IN, U));
		suppose($(_Z, IN, U));
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
				
				ebindTrim("definition_of_subset", _X, _Y);
				rewrite(h1, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), h3);
			
			{
				subdeduction();
				
				ebindTrim("definition_of_subset", _Y, _Z);
				rewrite(h2, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), name(-2));
			
			conclude();
		}
		
		{
			subdeduction();
			
			ebindTrim("definition_of_subset", _X, _Z);
			
			conclude();
		}
		
		rewriteRight(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void supposeTypeOfPowersetOfReals() {
		suppose("type_of_P_R",
				$(pp(R), SUBSET, U));
	}
	
	public static final void supposeRealsInUhm() {
		suppose("reals_in_Uhm",
				$(R, IN, U));
	}
	
	public static final void supposeDefinitionOfPositives() {
		final Object _n = $new("n");
		
		suppose("definition_of_positives", $forall(_n,
				$($(_n, IN, POS), "=", $($(_n, IN, N), LAND, $(0, "<", _n)))));
	}
	
	public static final void deducePositivesSubsetNaturals() {
		subdeduction("positives_subset_naturals");
		
		ebindTrim("definition_of_subset", POS, N);
		
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
	
	public static final void supposeDefinitionOfSingleton() {
		final Object _X = $new("X");
		
		suppose("definition_of_singleton",
				$forall(_X,
						$(_X, IN, c(_X))));
	}
	
	public static final void deducePositivesInUhm() {
		subdeduction("positives_in_Uhm");
		
		ebindTrim("subset_in_Uhm", POS, N);
		
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
												"=", $($(PI, "_", $(_i, "<", $(_n, "-", 1)), _X), "*", $(_X, "|", $1($(_i, "=", $(_n, "-", 1))), "@", $())))))));
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
	
	public static final void deduceNaturalsInUhm() {
		subdeduction("naturals_in_Uhm");
		
		ebindTrim("subset_in_Uhm", N, R);
		
		conclude();
	}
	
	public static final void simplifyElementaryExpression(final String targetName, final Object expression) {
		subdeduction();
		
		final Object simplified = ElementaryVerification.Evaluator.INSTANCE.apply(expression);
		
		verifyElementaryProposition($(expression, "=", simplified));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void testVectorAccess() {
		{
			subdeduction("vector_access.test1");
			
			computeVectorAccess(R, $(sequence(",", 1, 2, 3), "_", 1));
			
			conclude();
		}
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
		{
			subdeduction("vector_reduction_by_product.test1");
			
			computeVectorReductionByProduct($(PI, sequence(",", 1, 2, 3)));
			
			conclude();
		}
	}
	
	public static final void supposeDefinitionsForJavaCode() {
		/*
		 * (1)_i<2
		 * 
		 *   |
		 *   V
		 * 
		 * allocate("i",1);repeat(2,"i",0,()->{write("result",read("i",0),1)})
		 * 
		 * 
		 * forall X n
		 *   to_java (X)_i<n = allocate("i",1);repeat(n,"i",0,()->{write("result",read("i",0),to_java X)})
		 * 
		 * forall X in R
		 *   to_java X = X
		 * 
		 */
		
		{
			final Object _X = $new("X");
			final Object _i = $new("i");
			final Object _j = $new("j");
			final Object _n = $new("n");
			
			suppose("definition_of_vector_generator_to_java",
					$forall(_X, _i,
							$(FORALL, _n, IN, N,
									$rule($(FORALL, _j, IN, $(N, "_", $("<", _n)), $($(_X, "|", $1($(_i, "=", _j)), "@", $()), IN, R)),
											$($("to_java", $(p(_X), "_", $(_i, "<", _n))), "=", sequence(";",
													app("allocate", str("i"), 1),
													app("repeat", $("to_java", _n), str("i"), 0,
															block(app("write", str("result"), app("read", str("i"), 0) , $("to_java", _X))))))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_real_to_java",
					$(FORALL, _x, IN, R,
							$($("to_java", _x), "=", _x)));
		}
		
		{
			final String javacode = "javacode";
			
			{
				suppose("javacode_in_Uhm",
						$(javacode, IN, U));
			}
			
			{
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				suppose("sequence_in_javacode",
						$(FORALL, _p, ",", _q, IN, javacode,
								$(instructions(_p, _q), IN, javacode)));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				
				suppose("read_in_javacode",
						$forall(_a, _i,
								$(app("read", str(_a), _i), IN, javacode)));
			}
			
			{
				final Object _a = $new("a");
				final Object _n = $new("n");
				
				suppose("allocate_in_javacode",
						$forall(_a, _n,
								$(app("allocate", str(_a), _n), IN, javacode)));
			}
			
			
			{
				final Object _a = $new("a");
				final Object _n = $new("n");
				final Object _b = $new("b");
				final Object _i = $new("i");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _i));
				final Object instruction = app("allocate", str(_a), _n);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _i));
				
				suppose("meaning_of_allocate_0",
						$forall(_p, _a, _n, _b, _i,
								$rule($(LNOT, $(_a, "=", _b)), $(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _n = $new("n");
				final Object _i = $new("i");
				final Object _p = $new("p");
				
				final Object instruction = app("allocate", str(_a), _n);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_allocate_1",
						$forall(_a, _n, _i, _p,
								$rule($(_i, IN, $(N, "_", $("<", _n))),
										$(valueAfter, IN, R))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _x = $new("x");
				
				suppose("write_in_javacode",
						$forall(_a, _i, _x,
								$(app("write", str(_a), _i, _x), IN, javacode)));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _b = $new("b");
				final Object _j = $new("j");
				final Object _x = $new("x");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _j));
				final Object instruction = app("write", str(_a), _i, _x);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _j));
				
				suppose("meaning_of_write_0",
						$forall(_p, _a, _i, _b, _j, _x, 
								$rule($($(LNOT, $(_a, "=", _b)), LOR, $(LNOT, $(_i, "=", _j))),
										$(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _x = $new("x");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_a), _i));
				final Object instruction = app("write", str(_a), _i, _x);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_write_1",
						$forall(_a, _i, _x, _p,
								$rule($(_x, IN, R),
										$(valueBefore, IN, R),
										$(valueAfter, "=", _x))));
			}
			
			{
				final Object _n = $new("n");
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _q = $new("q");
				
				suppose("repeat_in_javacode",
						$forall(_n, _a, _i, _q,
								$(app("repeat", _n, str(_a), _i, $("()->{", _q, "}")), IN, javacode)));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _b = $new("b");
				final Object _j = $new("j");
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _j));
				final Object instruction = app("repeat", 0, str(_a), _i, $("()->{", _q, "}"));
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _j));
				
				suppose("meaning_of_repeat_0",
						$forall(_p, _a, _i, _b, _j, _q,
								$rule($($(LNOT, $(_a, "=", _b)), LOR, $(LNOT, $(_i, "=", _j))),
										$(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _n = $new("n");
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				final Object instruction = app("repeat", _n, str(_a), _i, $("()->{", _q, "}"));
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_repeat_1",
						$forall(_p, _n, _a, _i, _q,
								$rule($($(_n, IN, N)), $(valueAfter, "=", _n))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _n = $new("n");
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				final Object instruction = instructions(_p, app("repeat", _n, str(_a), _i, $("()->{", _q, "}")));
				final Object instruction2 = $("sequence_concatenate", ";",
						_p,
						$("sequence_concatenate", ";",
								$1(app("repeat", $(_n, "-", 1), str(_a), _i, $("()->{", _q, "}"))),
								_q));
				
				suppose("meaning_of_repeat_2",
						$forall(_p, _a, _i, _n, _q,
								$rule($($(_n, IN, POS)), $(instruction, "=", instruction2))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _p = $new("p");
				final Object _q = $new("q");
				final Object _r = $new("r");
				
				final Object valueAfterPQ = instructions(_p, _q, app("read", str(_a), _i));
				final Object valueAfterPR = instructions(_p, _r, app("read", str(_a), _i));
				
				suppose("definition_of_javacode_equality",
						$(FORALL, _p, ",", _q, IN, javacode,
								$($(_q, "=", _r), "=", $forall(_p, _a, _i, $(valueAfterPQ, "=", valueAfterPR)))));
			}
			
			{
				final Object _p = $new("p");
				final Object _f = $new("f");
				final Object _x = $new("x");
				final Object _a = $new("a");
				final Object _i = $new("i");
				
				final Object valueAfterP = instructions(_p, app("read", str(_a), _i));
				
				suppose("meaning_of_read_in_arguments",
						$forall(_p, _f, _x, _a, _i,
								$(instructions(_p, $(_f, "(", _x, ")")),
										"=", instructions(_p, $(_f, "(", $(_x, "|", $1($(app("read", str(_a), _i), "=", valueAfterP)), "@", $()), ")")))));
			}
		}
		
		{
			final Object _P = $new("P");
			final Object _n = $new("n");
			
			suppose("induction_principle",
					$forall(_P, _n,
							$rule($(_P, "|", $1($(_n, "=", 0)), "@", $()),
									$(FORALL, _n, IN, N, $rule(_P, $(_P, "|", $1($(_n, "=", $(_n, "+", 1))), "@", $()))),
									$(FORALL, _n, IN, N, _P))));
		}
		
		{
			final Object _X = $(1);
			final Object _i = $new("i");
			final Object _n = $new("n");
			final Object _p = $new("p");
			final Object _r = $(str("result"));
			final Object _j = $(0); // TODO var in 0 .. n - 1
			final Object _k = $new("k");
			
			newGoal("proof_of_to_java.test1",
					$forall(_n, $rule(
							$(_n, IN, POS),
							$(FORALL, _k, IN, $(N, "_", $("<", _n)), $($1(app("read", str("result"), _k)), IN, R)),
							$forall(_p, $rule($($("to_java", $(p(_X), "_", $(_i, "<", _n))), "=", _p),
									$(instructions(_p, app("read", _r, _j)), "=", $(_X, "|", $1($(_i, "=", _j)), "@", $())))))));
			
			goal().introduce();
			
			final Object _m = $new("m");
			
			bind("full_induction", "induction_principle", $(conclusion(goal().getProposition()), "|", $1($(_n, "=", $(1, "+", _m))), "@", $()), _m);
			
			{
				subdeduction("induction_condition_0_simplification");
				
				bind("identity", condition(proposition("full_induction")));
				simplifySubstitutionsAndForallInsAndElementary(proposition(-1), Simplifier.Mode.DEFINE);
				
				conclude();
			}
			
			{
				newGoal("induction_simplified_condition_0", right(proposition("induction_condition_0_simplification")));
				
				goal().introduce();
				
				{
					subdeduction();
					
					final Object p = forall("p");
					
					suppose($(left(condition(scope(goal().getProposition()))), "=", p));
					
					final String resultReality = name(-2);
					
					{
						subdeduction();
						
						new ToJavaHelper().compute(left(proposition(-1)));
						rewrite(name(-1), name(-2));
						
						conclude();
					}
					
					{
						subdeduction("replacement_of_repeat_1_q_with_repeat_0_q_q");
						
						{
							subdeduction();
							
							{
								final Variable vp0 = new Variable("p0");
								final Variable va = new Variable("a");
								final Variable vq = new Variable("q");
								
								matchOrFail(sequence(";", vp0, app("repeat", 1, str(va), 0, $("()->{", vq, "}"))), right(proposition(-1)));
								
								ebindTrim("meaning_of_repeat_2", $1(vp0.get()), va.get(), 0, 1, vq.get());
							}
							
							verifyElementaryProposition($($(1, "-", 1), "=", 0));
							rewrite(name(-2), name(-1));
							
							{
								final Variable va = new Variable("a");
								final Variable vb = new Variable("b");
								final Variable vc = new Variable("c");
								final Variable vd = new Variable("d");
								
								matchOrFail($($("sequence_append", ";", va, vb), "=",
										$("sequence_concatenate", ";", va, $("sequence_concatenate", ";", vc, vd))), proposition(-1));
								
								computeSequenceAppend(";", va.get(), vb.get());
								rewrite(name(-2), name(-1));
								
								computeSequenceConcatenate(";", vc.get(), vd.get());
								rewrite(name(-2), name(-1));
							}
							
							{
								final Variable va = new Variable("a");
								final Variable vb = new Variable("b");
								
								matchOrFail($("sequence_concatenate", ";", va, vb), right(proposition(-1)));
								
								computeSequenceConcatenate(";", va.get(), vb.get());
								rewrite(name(-2), name(-1));
							}
							
							conclude();
						}
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					{
						final Variable va = new Variable("a");
						final Variable vb = new Variable("b");
						final Variable vc = new Variable("c");
						
						matchOrFail(sequence(";", va, vb, vc), right(proposition(-1)));
						
						{
							subdeduction();
							
							{
								subdeduction();
								
								bind("meaning_of_read_in_arguments", sequence(";", va.get(), vb.get()), first(vc.get()), list(vc.get()).get(2), "i", 0);
								
								simplifySequenceAppendInLast();
								
								conclude();
							}
							
							{
								subdeduction();
								
								ebindTrim("meaning_of_repeat_1", $1(app("allocate", str("i"), 1)), 0, "i", 0, $1(app("write", str("result"), app("read", str("i"), 0), 1)));
								
								simplifySequenceAppendInLast();
								
								conclude();
							}
							
							rewrite(name(-2), name(-1));
							
							simplifySubstitutionsAndElementaryInLast();
							
							conclude();
						}
						
						rewrite(name(-2), name(-1));
						
						{
							subdeduction();
							
							{
								subdeduction();
								
								ebind("meaning_of_write_1", "result", 0, 1, sequence(";", app("allocate", str("i"), 1), app("repeat", 0, str("i"), 0, block(app("write", str("result"), app("read", str("i"), 0), 1)))));
								eapplyLast();
								
								simplifySequenceAppendInLast();
								
								conclude();
							}
							
							{
								subdeduction();
								
								bind("meaning_of_repeat_0",
										$1(app("allocate", str("i"), 1)),
										"i", 0, "result", 0,
										$1(app("write", str("result"), app("read", str("i"), 0), 1)));
								
								ebindTrim("left_elimination_of_disjunction", left(condition(proposition(-1))), right(condition(proposition(-1))), conclusion(proposition(-1)));
								
								simplifySequenceAppendInLast();
								
								{
									subdeduction();
									
									ebindTrim("meaning_of_allocate_0", $(), "i", 1, "result", 0);
									simplifySequenceAppendInLast();
									
									
									conclude();
								}
								
								rewriteRight(name(-2), name(-1));
								
								conclude();
							}
							
							rewriteRight(name(-2), name(-1));
							
							{
								subdeduction("result_element_is_real");
								
								{
									subdeduction();
									
									verifyElementaryProposition($(0, IN, N));
									verifyElementaryProposition($(0, "<", 1));
									ebindTrim("introduction_of_conjunction", proposition(-2), proposition(-1));
									
									ebindTrim("definition_of_range", 1, 0);
									rewriteRight(name(-2), name(-1));
									
									conclude();
								}
								
								ebindTrim(resultReality, 0);
								
								conclude();
							}
							
							eapply(name(-2));
							
							final List<Object> l = flattenSequence(";", left(proposition(-1)));
							
							computeSequenceAppend(";", sequence(";", l.subList(0, l.size() - 1).toArray()), last(l));
							
							rewriteRight(name(-2), name(-1));
							
							conclude();
						}
						
						rewriteRight(name(-1), name(-2));
					}
					
					conclude();
				}
				
				concludeGoal();
			}
			
			rewriteRight("induction_condition_0", "induction_simplified_condition_0", "induction_condition_0_simplification");
			
			{
				subdeduction("induction_condition_n_simplification");
				
				bind("identity", condition(conclusion(proposition("full_induction"))));
				simplifySubstitutionsAndForallInsAndElementary(proposition(-1), Simplifier.Mode.DEFINE);
				
				conclude();
			}
			
			{
				newGoal("induction_simplified_condition_n", right(proposition("induction_condition_n_simplification")));
				
				final Object m = goal().introduce();
				goal().introduce();
				goal().introduce();
				goal().introduce();
				
				{
					subdeduction();
					
					final Object p = forall("p");
					
					suppose($(left(condition(scope(goal().getProposition()))), "=", p));
					
					final String resultReality = name(-2);
					
					final String definitionOfP = name(-1);
					
					deduceNaturalIsReal(m);
					
					{
						subdeduction();
						
						new ToJavaHelper().compute(left(proposition(definitionOfP)));
						rewrite(name(-1), definitionOfP);
						simplifyArithmeticInLast();
						
						conclude();
					}
					
					{
						subdeduction();
						
						{
							subdeduction();
							
							{
								subdeduction();
								
								ebindTrim("nonnegativity_of_naturals", m);
								ebindTrim("preservation_of_" + LE + "_under_addition", left(proposition(-1)), right(proposition(-1)), 1);
								ebindTrim("preservation_of_" + LE + "_under_addition", left(proposition(-1)), right(proposition(-1)), 1);
								ebindTrim("commutativity_of_addition", left(right(proposition(-1))), right(right(proposition(-1))));
								rewrite(name(-2), name(-1));
								simplifySubstitutionsAndElementaryInLast(Simplifier.Mode.REWRITE);
								ebindTrim("transitivity_of_<" + LE, 0, left(proposition(-1)), right(proposition(-1)));
								
								conclude();
							}
							
							ebindTrim("meaning_of_repeat_2",
									sequence(";", app("allocate", str("i"), 1)), "i", 0, $(1, "+", $(m, "+", 1)),
									sequence(";", app("write", str("result"), app("read", str("i"), 0), 1)));
							
							simplifySequenceAppendInLast();
							simplifySequenceConcatenateInLast();
							simplifyArithmeticInLast();
							
							conclude();
						}
						
						rewrite(name(-2), name(-1));
						
						{
							subdeduction();
							
							final Variable vp0 = new Variable("p0");
							final Variable vp1 = new Variable("p1");
							final Variable vf = new Variable("f");
							final Variable vx = new Variable("x");
							
							matchOrFail(sequence(";", vp0, vp1, $(vf, "(", vx, ")")), right(proposition(-1)));
							
							final Object pp = sequence(";", vp0.get(), vp1.get());
							
							bind("meaning_of_read_in_arguments",
									pp,
									vf.get(),
									vx.get(),
									"i",
									0);
							
							simplifySequenceAppendInLast();
							
							{
								subdeduction();
								
								ebindTrim("meaning_of_repeat_1",
										sequence(";", vp0.get()),
										$(1, "+", m),
										"i",
										0,
										sequence(";", $(vf.get(), "(", vx.get(), ")")));
								simplifySequenceAppendInLast();
								
								conclude();
							}
							
							rewrite(name(-2), name(-1));
							
							simplifySubstitutionsAndElementaryInLast();
							
							conclude();
						}
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					{
						subdeduction();
						
						computeSequenceAppend(";", right(proposition(-1)), app("read", str("result"), 0));
						
						rewriteRight(name(-1), name(-2));
						
						conclude();
					}
					
					{
						subdeduction();
						
						final Variable vp0 = new Variable("p0");
						final Variable vp1 = new Variable("p1");
						final Variable va = new Variable("a");
						final Variable vi = new Variable("i");
						
						matchOrFail($(sequence(";", vp0, vp1, app("write", str(va), vi, 1))), right(proposition(-2)));
						
						ebind("meaning_of_write_0",
								sequence(";", vp0.get(), vp1.get()),
								va.get(),
								vi.get(),
								va.get(),
								0,
								1);
						
						simplifySequenceAppendInLast();
						
						{
							subdeduction();
							
							ebindTrim("nonnegativity_of_naturals", m);
							ebindTrim("preservation_of_" + LE + "_under_addition", left(proposition(-1)), right(proposition(-1)), 1);
							ebindTrim("transitivity_of_<" + LE, 0, left(proposition(-1)), right(proposition(-1)));
							ebindTrim("commutativity_of_addition", left(right(proposition(-1))), right(right(proposition(-1))));
							rewrite(name(-2), name(-1));
							ebindTrim("conversion<>", left(proposition(-1)), right(proposition(-1)));
							rewrite(name(-2), name(-1));
							ebindTrim(">_implies_not_equal", left(proposition(-1)), right(proposition(-1)));
							
							conclude();
						}
						
						{
							final Variable vx = new Variable("x");
							final Variable vy = new Variable("y");
							final Variable vz = new Variable("z");
							
							matchOrFail($rule($(vx, LOR, vy), vz), proposition(-2));
							
							ebindTrim("right_elimination_of_disjunction", vx.get(), vy.get(), vz.get());
						}
						
						ebindTrim("commutativity_of_equality", left(proposition(-1)), right(proposition(-1)));
						
						conclude();
					}
					
					rewrite(name(-2), name(-1));
					
					{
						subdeduction("meaning_of_prefix");
						
						{
							subdeduction();
							
							final Object k = forall("k");
							
							suppose($(k, IN, $(N, "_", $("<", $(1, "+", m)))));
							
							final String h = name(-1);
							
							bind("induction_simplified_condition_n.3", k);
							
							{
								subdeduction();
								
								ebindTrim("definition_of_range", $(1, "+", $(m, "+", 1)), k);
								
								{
									subdeduction();
									
									ebindTrim("definition_of_range", $(1, "+", m), k);
									rewrite(h, name(-1));
									breakConjunction(name(-1));
									
									{
										subdeduction();
										
										ebindTrim("preservation_of_<_under_addition", 0, 1, m);
										ebindTrim("commutativity_of_addition", 0, m);
										rewrite(name(-2), name(-1));
										ebindTrim("commutativity_of_addition", 1, m);
										rewrite(name(-2), name(-1));
										ebindTrim("neutrality_of_0", m);
										rewrite(name(-2), name(-1));
										
										ebindTrim("preservation_of_<_under_addition", m, $(m, "+", 1), 1);
										ebindTrim("commutativity_of_addition", m, 1);
										rewrite(name(-2), name(-1), 0);
										ebindTrim("commutativity_of_addition", $(m, "+", 1), 1);
										rewrite(name(-2), name(-1));
										
										deduceNaturalIsReal(k);
										
										ebindTrim("transitivity_of_<", k, $(1, "+", m), $(1, "+", $(m, "+", 1)));
										
										conclude();
									}
									
									ebindTrim("introduction_of_conjunction", proposition(-3), proposition(-1));
									
									conclude();
								}
								
								rewriteRight(name(-1), name(-2));
								
								conclude();
							}
							
							eapply(name(-2));
							
							conclude();
						}
						
//						canonicalizeForallIn(condition(proposition("induction_condition_n.2")));
//						
//						rewriteRight(name(-2), name(-1));
						
						eapply("induction_simplified_condition_n.2");
						
						new ToJavaHelper().compute(left(condition(scope(proposition(-1)))));
						ebindTrim(name(-2), right(proposition(-1)));
						simplifySequenceAppendInLast();
						
						conclude();
					}
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				concludeGoal();
			}
			
			rewriteRight("induction_condition_n", "induction_simplified_condition_n", "induction_condition_n_simplification");
			
			goal().introduce();
			
			{
				subdeduction();
				
				ebindTrim("definition_of_positives", _n);
				rewrite(last(deduction().getParent().getConditionNames()), name(-1));
				
				conclude();
			}
			
			breakConjunction(name(-1));
			
			{
				subdeduction("n_is_relative");
				
				ebindTrim("definition_of_subset", N, Z);
				rewrite("naturals_subset_relatives", name(-1));
				ebindTrim(name(-1), _n);
				
				conclude();
			}
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					ebindTrim("definition_of_subset", N, Z);
					rewrite("naturals_subset_relatives", name(-1));
					ebindTrim(name(-1), _n);
					
					ebindTrim("equality_<" + LE, 0, _n);
					
//					simplifyArithmeticInLast(); // FIXME stack pops too far
					
					conclude();
				}
				
				rewrite(name(-3), name(-1));
				simplifyArithmeticInLast();
				
				conclude();
			}
			
			{
				subdeduction("n_is_real");
				
				ebindTrim("definition_of_subset", N, R);
				rewrite("naturals_subset_reals", name(-1));
				ebindTrim(name(-1), _n);
				
				conclude();
			}
			
			{
				subdeduction();
				
				trim("full_induction");
				
				canonicalizeForallIn(proposition(-1));
				
				rewrite(name(-2), name(-1));
				
				bind(name(-1), $(_n, "-", 1));
				
				ebindTrim("subtraction_in_naturals", _n, 1);
				
				eapply(name(-2));
				
				simplifyArithmeticInLast();
				
				ebindTrim("commutativity_of_addition", 0, _n);
				rewrite(name(-2), name(-1));
				
				ebindTrim("neutrality_of_0", _n);
				rewrite(name(-2), name(-1));
				
				{
					final Variable vX = new Variable("X");
					final Variable ve = new Variable("e");
					
					matchOrFail($(vX, "|", ve, "@", $()), proposition(-1));
					
					substitute(vX.get(), toMap(ve.get()));
					rewrite(name(-2), name(-1));
				}
				
				conclude();
			}
			
			concludeGoal();
		}
	}

	public static void deduceNaturalIsReal(final Object value) {
		subdeduction();
		
		ebindTrim("definition_of_subset", N, R);
		
		rewrite("naturals_subset_reals", name(-1));
		
		ebindTrim(name(-1), value);
		
		conclude();
	}
	
	public static final void simplifySubstitutionsAndForallInsAndElementary(final Object expression, final Simplifier.Mode mode) {
		new Simplifier(mode)
		.add(newElementarySimplificationRule())
		.add(newSubstitutionSimplificationRule())
		.add(newForallInSimplificationRule())
		.add(newForallIn2SimplificationRule())
		.add(newForallIn3SimplificationRule())
		.add(rule(new Variable("*"), (e, m) -> false))
		.simplifyCompletely(expression);
	}
	
	public static final void simplifySubstitutionsAndElementaryInLast() {
		simplifySubstitutionsAndElementaryInLast(Simplifier.Mode.DEFINE);
	}
	
	public static final void simplifySubstitutionsAndElementaryInLast(final Simplifier.Mode mode) {
		new Simplifier(mode)
				.add(newElementarySimplificationRule())
				.add(newSubstitutionSimplificationRule())
				.add(rule(new Variable("*"), (e, m) -> false))
				.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceAppendInLast() {
		new Simplifier()
				.add(newSequenceAppendSimplificationRule())
				.add(rule(new Variable("*"), (e, m) -> false))
				.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceConcatenateInLast() {
		new Simplifier()
				.add(newSequenceConcatenateSimplificationRule())
				.add(rule(new Variable("*"), (e, m) -> false))
				.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifyArithmeticInLast() {
		final Simplifier simplifier = new Simplifier();
		
		simplifier.add(newElementarySimplificationRule());
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable vz = new Variable("z");
			
			simplifier.add(new SimpleRule<>(
					(e, m) -> {
						if (match($($(vx, "+", vy), "+", vz), e)) {
							final Object y = vy.get();
							final Object z = vz.get();
							final Number ny = cast(Number.class, y);
							final Number nz = cast(Number.class, z);
							
							if (ny == null && nz != null) {
								return true;
							}
							
							if (ny == null && nz == null && y.toString().compareTo(z.toString()) > 0) {
								return true;
							}
						}
						
						return false;
					}, (e, m) -> {
						{
							subdeduction();	
							
							ebindTrim("associativity_of_addition", vx.get(), vy.get(), vz.get());
							ebindTrim("commutativity_of_addition", vy.get(), vz.get());
							rewrite(name(-2), name(-1));
							
							conclude();
						}
						
						return true;
					}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable vz = new Variable("z");
			
			simplifier.add(new SimpleRule<>(
					(e, m) -> {
						if (match($(vx, "+", $(vy, "+", vz)), e)) {
							return true;
						}
						
						return false;
					}, (e, m) -> {
						{
							subdeduction();	
							
							ebindTrim("associativity_of_addition", vx.get(), vy.get(), vz.get());
							ebindTrim("commutativity_of_equality", left(proposition(-1)), right(proposition(-1)));
							
							conclude();	
						}
						
						return true;
					}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			simplifier.add(new SimpleRule<>(
					(e, m) -> {
						if (match($($(vx, "-", vy)), e)) {
							return true;
						}
						
						return false;
					}, (e, m) -> {
						ebindTrim("definition_of_subtraction", vx.get(), vy.get());
						
						return true;
					}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			simplifier.add(new SimpleRule<>(
					(e, m) -> {
						if (match($($(vx, "+", vy)), e)) {
							final Object x = vx.get();
							final Object y = vy.get();
							final Number nx = cast(Number.class, x);
							final Number ny = cast(Number.class, y);
							
							if (nx == null && ny != null) {
								return true;
							}
							
							if (nx == null && ny == null && x.toString().compareTo(y.toString()) > 0) {
								return true;
							}
						}
						
						return false;
					}, (e, m) -> {
						ebindTrim("commutativity_of_addition", vx.get(), vy.get());
						
						return true;
					}));
		}
		
		simplifier.add(rule(new Variable("*"), (e, m) -> false));
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	/**
	 * @author codistmonk (creation 2016-08-21)
	 */
	public static final class Simplifier implements ExpressionVisitor<Boolean> {
		
		private final Rules<Object, Boolean> rules;
		
		private final Mode mode;
		
		public Simplifier() {
			this(Mode.REWRITE);
		}
		
		public Simplifier(final Mode mode) {
			this.rules = new Rules<>();
			this.mode = mode;
		}
		
		public final Rules<Object, Boolean> getRules() {
			return this.rules;
		}
		
		public final Mode getMode() {
			return this.mode;
		}
		
		public final Simplifier add(final Rule<Object, Boolean> rule) {
			this.getRules().add(rule);
			
			return this;
		}
		
		public final void simplifyCompletely(final Object expression) {
			subdeduction();
			
			if (this.apply(expression)) {
				while (this.apply(proposition(-1))) {
					// NOP
				}
			} else {
				pop();
			}
			
			conclude();
		}
		
		@Override
		public final Boolean visit(final Object expression) {
			return this.tryRules(expression);
		}
		
		@Override
		public final Boolean visit(final List<?> expression) {
			if (this.tryRules(expression)) {
				return true;
			}
			
			for (final Object subExpression : expression) {
				if (this.apply(subExpression)) {
					return true;
				}
			}
			
			return false;
		}
		
		private final boolean tryRules(final Object expression) {
			final Deduction deduction = subdeduction();
			
			try {
				if (this.getRules().applyTo(expression)) {
					if (Mode.DEFINE.equals(this.getMode())) {
						final int targets = countIn(proposition(-2), left(proposition(-1)));
						final int leftTargets = countIn(left(proposition(-2)), left(proposition(-1)));
						
						if (leftTargets < targets) {
							final int[] rightTargets = new int[targets - leftTargets];
							
							for (int i = leftTargets; i < targets; ++i) {
								rightTargets[i - leftTargets] = i;
							}
							
							rewrite(name(-2), name(-1), rightTargets);
						} else {
							popTo(deduction.getParent());
							
							return false;
						}
					} else {
						rewrite(name(-2), name(-1));
					}
					
					conclude();
					
					return true;
				}
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			popTo(deduction.getParent());
			
			return false;
		}
		
		private static final long serialVersionUID = -5429351197907942483L;
		
		public static final void popTo(final Deduction deduction) {
			while (deduction() != deduction) {
				pop();
			}
		}
		
		public static final int countIn(final Object target, final Object pattern) {
			return new ExpressionVisitor<Integer>() {
				
				@Override
				public final Integer visit(final Object expression) {
					if (new Substitution.ExpressionEquality().apply(pattern, expression)) {
						return 1;
					}
					
					return 0;
				}
				
				@Override
				public final Integer visit(final List<?> expression) {
					final Integer result = this.visit((Object) expression);
					
					return 0 < result ? result : expression.stream().mapToInt(this::apply).sum();
				}
				
				private static final long serialVersionUID = 2608876360859599240L;
				
			}.apply(target);
		}
		
		/**
		 * @author codistmonk (creation 2016-08-23)
		 */
		public static enum Mode {
			
			REWRITE, DEFINE;
			
		}
		
	}
	
	public static final SimpleRule<Object, Boolean> newSequenceAppendSimplificationRule() {
		final Variable vs = new Variable("s");
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		
		return rule($("sequence_append", vs, vx, vy), (e, m) -> {
			computeSequenceAppend(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newSequenceConcatenateSimplificationRule() {
		final Variable vs = new Variable("s");
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		
		return rule($("sequence_concatenate", vs, vx, vy), (e, m) -> {
			computeSequenceConcatenate(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newSubstitutionSimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable ve = new Variable("e");
		final Variable vi = new Variable("i");
		
		return rule($(vx, "|", ve, "@", vi), (e, m) -> {
			substitute(vx.get(), toMap(ve.get()), toInts(vi.get()));
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newForallInSimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		return rule($(FORALL, vx, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in", vx.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newForallIn2SimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		return rule($(FORALL, vx, ",", vy, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in_2", vx.get(), vy.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newForallIn3SimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vz = new Variable("z");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		return rule($(FORALL, vx, ",", vy, ",", vz, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in_3", vx.get(), vy.get(), vz.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final SimpleRule<Object, Boolean> newElementarySimplificationRule() {
		return new SimpleRule<>((e, m) -> {
			try {
				final Object f = ElementaryVerification.Evaluator.INSTANCE.apply(e);
				
				return !f.equals(e) && !Substitution.deepContains(f, null);
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			return false;
		}, (e, m) -> {
			try {
				final Object f = ElementaryVerification.Evaluator.INSTANCE.apply(e);
				
				verifyElementaryProposition($(e, "=", f));
				
				return true;
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			return false;
		});
	}
	
	public static final int[] toInts(final Object indices) {
		return list(indices).stream().mapToInt(i -> ((Number) i).intValue()).toArray(); 
	}
	
	public static final Map<Object, Object> toMap(final Object equalities) {
		final Map<Object, Object> result = new LinkedHashMap<>();
		
		for (final Object equality : list(equalities)) {
			result.put(left(equality), right(equality));
		}
		
		return result;
	}
	
	public static final void supposeDefinitionsForCLCode() {
		{
			final Object _X = $new("X");
			final Object _i = $new("i");
			final Object _j = $new("j");
			final Object _n = $new("n");
			
			suppose("definition_of_vector_generator_to_CL",
					$forall(_X, _i,
							$(FORALL, _n, IN, N,
									$rule($(FORALL, _j, IN, $(N, "_", $("<", _n)), $($(_X, "|", $1($(_i, "=", _j)), "@", $()), IN, R)),
											$($("to_CL", $(p(_X), "_", $(_i, "<", _n))), "=", sequence(";\n",
													"	int const gid = get_global_id(0)",
													$("	result[gid] = ", $($("to_CL", _X), "|", $1($(_i, "=", "gid")), "@", $())),
													""))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_real_to_CL",
					$(FORALL, _x, IN, R,
							$($("to_CL", _x), "=", _x)));
		}
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
	
	public static final void supposeVectorTypeInUhm() {
		final Object _X = $new("X");
		final Object _n = $new("n");
		
		suppose("vector_type_in_Uhm",
				
				$(FORALL, _X, IN, U,
						$(FORALL, _n, IN, N,
								$($(_X, "^", _n), IN, U))));
	}
	
	public static final void supposeTypeOfSingle() {
		final Object _X = $new("X");
		final Object _x = $new("x");
		
		suppose("type_of_single",
				$(FORALL, _X, IN, U,
						$forall(_x,
								$($(_x, IN, _X), "=", $($1(_x), IN, $1(_X))))));
	}
	
	public static final void supposeTypeOfSingleInUhm() {
		final Object _X = $new("X");
		
		suppose("type_of_single_in_Uhm",
				$(FORALL, _X, IN, U,
						$($1(_X), IN, U)));
	}
	
	public static final void supposeTypeOfTuple() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		final Object _x = $new("x");
		final Object _y = $new("y");
		
		suppose("type_of_tuple",
				$(FORALL, _X, ",", _Y, IN, U,
						$(FORALL, _x, IN, _X,
								$(FORALL, _y, IN, _Y,
										$($("sequence_append", ",", _x, _y), IN, $("sequence_append", CROSS, _X, _Y))))));
	}
	
	public static final void supposeTypeOfTupleInUhm() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("type_of_tuple_in_Uhm",
				$(FORALL, _X, ",", _Y, IN, U,
						$($("sequence_append", CROSS, _X, _Y), IN, U)));
	}
	
	public static final void testTypeOfTuple() {
		{
			subdeduction("type_of_tuple.test1");
			
			{
				subdeduction();
				
				verifyElementaryProposition($(1, IN, N));
				
				ebindTrim("type_of_single", N, 1);
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			ebindTrim("type_of_tuple", $1(N), N, $1(1), 2);
			
			final List<?> _x = list(left(proposition(-1)));
			final List<?> _X = list(right(proposition(-1)));
			
			computeSequenceAppend(_x.get(1), _x.get(2), _x.get(3));
			rewrite(name(-2), name(-1));
			
			computeSequenceAppend(_X.get(1), _X.get(2), _X.get(3));
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("type_of_tuple.test2");
			
			{
				subdeduction();
				
				ebindTrim("type_of_tuple_in_Uhm", $1(N), N);
				
				computeSequenceAppend(CROSS, $1(N), N);
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			ebindTrim("type_of_tuple", sequence(CROSS, N, N), N, sequence(",", 1, 2), 3);
			
			final List<?> _x = list(left(proposition(-1)));
			final List<?> _X = list(right(proposition(-1)));
			
			computeSequenceAppend(_x.get(1), _x.get(2), _x.get(3));
			rewrite(name(-2), name(-1));
			
			computeSequenceAppend(_X.get(1), _X.get(2), _X.get(3));
			rewrite(name(-2), name(-1));
			
			conclude();
		}
	}
	
	public static final void supposeDefinitionsForRepeat() {
		{
			final Object _s = $new("s");
			final Object _x = $new("x");
			
			suppose("definition_of_repeat_0",
					$forall(_s, _x,
							$($("repeat", _s, _x, 0), "=", $())));
		}
		
		{
			final Object _s = $new("s");
			final Object _x = $new("x");
			final Object _n = $new("n");
			
			suppose("definition_of_repeat_n",
					$forall(_s, _x,
							$(FORALL, _n, IN, POS,
									$($("repeat", _s, _x, _n), "=", $("sequence_append", _s, $("repeat", _s, _x, $(_n, "-", 1)), _x)))));
		}
	}
	
	public static final void supposeSimplificationOfTypeOfTuple() {
		final Object _n = $new("n");
		final Object _X = $new("X");
		
		suppose("simplification_of_type_of_tuple",
				$(FORALL, _X, IN, U,
						$(FORALL, _n, IN, N,
								$($("repeat", CROSS, _X, _n), "=", $(_X, "^", _n)))));
	}
	
	public static final void testSimplificationOfTypeOfTuple() {
		{
			subdeduction("simplification_of_type_of_tuple.test1");
			
			ebindTrim("simplification_of_type_of_tuple", N, 3);
			
			new RepeatHelper(CROSS, N, 3).compute();
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("simplification_of_type_of_tuple.test2");
			
			rewrite("type_of_tuple.test2", "simplification_of_type_of_tuple.test1");
			
			conclude();
		}
	}
	
	public static final void supposeDefinitionsForVectorAccess() {
		{
			final Object _x = $new("x");
			final Object _X = $new("X");
			final Object _n = $new("n");
			
			suppose("definition_of_vector_access_0",
					$(FORALL, _X, IN, U,
							$(FORALL, _n, IN, POS,
									$(FORALL, _x, IN, $(_X, "^", _n),
											$($(_x, "_", 0), "=", $("sequence_head", _x))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _X = $new("X");
			final Object _n = $new("n");
			final Object _i = $new("i");
			
			suppose("definition_of_vector_access_i",
					$(FORALL, _X, IN, U,
							$(FORALL, _n, ",", _i, IN, POS,
									$(FORALL, _x, IN, $(_X, "^", _n),
											$($(_x, "_", _i), "=", $($("sequence_tail", ",", _x), "_", $(_i, "-", 1)))))));
		}
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
				ebind("definition_of_repeat_0", this.s, this.x);
			} else {
				subdeduction();
				
				{
					subdeduction();
					
					ebindTrim("definition_of_repeat_n", this.s, this.x, this.n);
					verifyElementaryProposition($($(this.n, "-", 1), "=", this.n - 1));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				new RepeatHelper(this.s, this.x, this.n - 1).compute();
				rewrite(name(-2), name(-1));
				
				final List<?> formula = list(right(proposition(-1)));
				
//				new SequenceAppendHelper_(this.s, formula.get(2), formula.get(3)).compute();
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
	
	/**
	 * @author codistmonk (creation 2016-08-18)
	 */
	public static final class ToCLHelper implements Serializable {
		
		private final Rules<Object, Void> rules = new Rules<>();
		
		{
			{
				final Variable vX = new Variable("X");
				final Variable vi = new Variable("i");
				final Variable vn = new Variable("n");
				
				this.rules.add(rule($("to_CL", $(p(vX), "_", $(vi, "<", vn))), (__, m) -> {
					final Object _X = m.get(vX);
					final Object _i = m.get(vi);
					final Object _n = m.get(vn);
					
					ebind("definition_of_vector_generator_to_CL", _X, _i, _n);
					eapplyLast();
					
					{
						subdeduction();
						
						{
							subdeduction();
							
							final Object j = second(left(proposition(-1)));
							
							{
								subdeduction();
								
								final Object _j = forall("j");
								
								suppose($(_j, IN, $(N, "_", $("<", _n))));
								
								substitute(_X, map(_i, _j));
								
								{
									final Object proposition = $(right(proposition(-1)), IN, R);
									final PropositionDescription justication = justicationFor(proposition);
									
									rewriteRight(justication.getName(), name(-2));
								}
								
								conclude();
							}
							
							{
								ebind("definition_of_forall_in", j, $(N, "_", $("<", _n)), $($(_X, "|", $1($(_i, "=", j)), "@", $()), IN, R));
								
								rewriteRight(name(-2), name(-1));
							}
							
							conclude();
						}
						
						eapply(name(-2));
						
						this.rules.applyTo($("to_CL", _X));
						rewrite(name(-2), name(-1));
						
						substitute(_X, map(_i, "gid"));
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					return null;
				}));
			}
			
			{
				final Variable vX = new Variable("X");
				
				this.rules.add(rule($("to_CL", vX), (__, m) -> {
					ebindTrim("definition_of_real_to_CL", m.get(vX));
					
					return null;
				}));
			}
		}
		
		public final void compute(final Object proposition) {
			this.rules.applyTo(proposition);
		}
		
		private static final long serialVersionUID = 3834061141856389415L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-18)
	 */
	public static final class ToJavaHelper implements Serializable {
		
		private final Rules<Object, Void> rules = new Rules<>();
		
		{
			{
				final Variable vX = new Variable("X");
				final Variable vi = new Variable("i");
				final Variable vn = new Variable("n");
				
				this.rules.add(rule($("to_java", $(p(vX), "_", $(vi, "<", vn))), (__, m) -> {
					final Object _X = m.get(vX);
					final Object _i = m.get(vi);
					final Object _n = m.get(vn);
					
					{
						subdeduction();
						
						ebind("definition_of_vector_generator_to_java", _X, _i, _n);
						eapplyLast();
						
						{
							subdeduction();
							
							final Object j = second(left(proposition(-1)));
							
							{
								subdeduction();
								
								final Object _j = forall("j");
								
								suppose($(_j, IN, $(N, "_", $("<", _n))));
								
								substitute(_X, map(_i, _j));
								
								{
									final Object proposition = $(right(proposition(-1)), IN, R);
									final PropositionDescription justication = justicationFor(proposition);
									
									rewriteRight(justication.getName(), name(-2));
								}
								
								conclude();
							}
							
							{
								ebind("definition_of_forall_in", j, $(N, "_", $("<", _n)), $($(_X, "|", $1($(_i, "=", j)), "@", $()), IN, R));
								
								rewriteRight(name(-2), name(-1));
							}
							
							conclude();
						}
						
						eapply(name(-2));
						
						{
							this.rules.applyTo($("to_java", _n));
							
							rewrite(name(-2), name(-1));
						}
						
						{
							this.rules.applyTo($("to_java", _X));
							
							rewrite(name(-2), name(-1));
						}
						
						conclude();
					}
					
					return null;
				}));
			}
			
			{
				final Variable vX = new Variable("X");
				
				this.rules.add(rule($("to_java", vX), (__, m) -> {
					ebindTrim("definition_of_real_to_java", m.get(vX));
					
					return null;
				}));
			}
		}
		
		public final void compute(final Object expression) {
			this.rules.applyTo(expression);
		}
		
		private static final long serialVersionUID = 8767164056521982370L;
		
	}
	
}
