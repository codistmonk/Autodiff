package autodiff.nodes;

import static autodiff.reasoning.deductions.Standard.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.BasicNumericVerification;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Substitution;
import autodiff.reasoning.tactics.Goal;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
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
			this.boundForm = Standard.build(new Deduction(
					AUTODIFF, this.getName() + "_bind"), this.getBinder(), 1);
		}
		
		return this.boundForm;
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object U = $("℧");
	
	public static final Object IN = $("∈");
	
	public static final Object SUBSET = $("⊂");
	
	public static final Object EQUIV = $("⇔");
	
	public static final Object P = $("ℙ");
	
	public static final Object CROSS = $("×");
	
	public static final Object TCROSS = $("¤");
	
	public static final Object UML = $("¨");

	public static final Object PI = $("Π");
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Object cases(final Object... cases) {
		return sequence("", append(array((Object) "cases"), cases));
	}
	
	public static final Deduction AUTODIFF = Standard.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Standard.setup();
			
//			debugPrint(sequence(",", $(1, 2, 3)));
//			debugPrint(sequence(",", 1));
//			debugPrint(sequence(",", 1, 2));
//			debugPrint(sequence(",", 1, 2, 3));
//			debugPrint(sequence(",", 1, sequence(",", 2, 3)));
//			debugPrint(sequence(",", sequence(",", 1, 2), 3));
//			debugPrint(sequence(",", 1, sequence(",", 2, 3), 4));
//			debugPrint(sequence(",", 1, 2, 3, 4));
			
			supposeEliminationOfParentheses();
			supposeDefinitionOfForallIn();
			supposeDefinitionOfForallIn2();
			supposeDefinitionOfForallIn3();
			
			supposeIntroductionOfConjunction();
			supposeLeftEliminationOfConjunction();
			supposeRightEliminationOfConjunction();
			supposeDefinitionOfLogicalEquivalence();
			supposeLogicalEquality();
			deduceLogicalEquivalenceImpliesLogicalEquality();
			deduceCommutativityOfConjunction();
			
			supposeDefinitionOfSubset();
			supposeDefinitionOfPowerset();
			supposeSubsetInUhm();
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
			
			{
				final Object _s = $new("s");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("definition_of_sequence_new",
						$forall(_s, _x, _y,
								$($("sequence_new", _s, _x, _y), "=", $(_x, $(_s, _y)))));
			}
			
			supposeEliminationsOfCases();
			testEliminationOfCases();
			
			supposeDefinitionsForSequenceAppend();
			testSequenceAppend();
			
			supposeDefinitionsForSequenceConcatenate();
			testSequenceConcatenate();
			
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
			
			supposeDefinitionsForSequenceHead();
			
			supposeDefinitonsForSequenceTail();
			
			testSequenceHead();
			
			supposeDefinitionsForVectorAccess();
			
			testVectorAccess();
			
			supposeDefinitionOfVectorReductionByProduct();
			
			testVectorReductionByProduct();
			
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
					simplifyBasicNumericExpression(name(-1), right(right(proposition(-1))));
					
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
							
							simplifyBasicNumericExpression(name(-1), right(proposition(-1)));
							
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
							
							simplifyBasicNumericExpression(name(-1), right(proposition(-1)));
							
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
	
	public static final void computeSequenceHead(final Object x) {
		final List<?> list = list(x);
		
		if (1 == list.size()) {
			ebind("definition_of_sequence_head_1", first(list));
			
			return;
		}
		
		if (2 == list.size()) {
			ebind("definition_of_sequence_head_2", first(list), second(list));
			
			return;
		}
		
		throw new IllegalArgumentException();
	}
	
	public static final void computeSequenceTail(final Object separator, final Object x) {
		final List<?> list = list(x);
		
		if (2 == list.size()) {
			final List<?> second = list(second(list));
			
			if (separator.equals(first(second))) {
				if (2 == second.size()) {
					ebind("definition_of_sequence_tail_1", separator, first(list), second(second));
					
					return;
				}
				
				if (3 == second.size()) {
					ebind("definition_of_sequence_tail_2", separator, first(list), second(second), third(second));
					
					return;
				}
			}
		}
		
		throw new IllegalArgumentException();
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
	
	public static final void deduceCartesianProduct(final Object valueType, final Object... values) {
		subdeduction();
		
		beginCartesianProduct(values[0], valueType);
		
		for (int i = 1; i < values.length; ++i) {
			appendToCartesianProduct(values[i], valueType);
		}
		
		{
			subdeduction();
			
			ebindTrim("simplification_of_type_of_tuple", valueType, values.length);
			
			new RepeatHelper(CROSS, valueType, values.length).compute();
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void beginCartesianProduct(final Object value,
			final Object type) {
		subdeduction();
		
		deduceSingleType(justicationFor($(value, IN, type)).getName());
		
		conclude();
	}
	
	public static final void appendToCartesianProduct(final Object value, final Object type) {
		final Object previousValue = left(proposition(-1));
		final Object previousType = right(proposition(-1));
		
		{
			subdeduction();
			
			ebindTrim("type_of_tuple_in_Uhm", previousType, type);
			
//			new SequenceAppendHelper(CROSS, previousType, type).compute();
			computeSequenceAppend(CROSS, previousType, type);
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction();
			
			deducePositivity(1);
			
			ebindTrim("type_of_tuple", previousType, type, previousValue, value);
			
//			new SequenceAppendHelper(",", previousValue, value).compute();
			computeSequenceAppend(",", previousValue, value);
			rewrite(name(-2), name(-1));
			
//			new SequenceAppendHelper(CROSS, previousType, type).compute();
			computeSequenceAppend(CROSS, previousType, type);
			rewrite(name(-2), name(-1));
			
			conclude();
		}
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
	
	public static final List<Object> p(final Object... objects) {
		return list($("(", $(objects), ")"));
	}
	
	public static final List<Object> c(final Object... objects) {
		return list($("{", $(objects), "}"));
	}
	
	public static final void deducePositivity(final Object target) {
		subdeduction();
		
		bind("definition_of_positives", target);
		
		{
			subdeduction();
			
			verifyBasicNumericProposition($(target, IN, N));
			verifyBasicNumericProposition($(0, "<", target));
			
			bind("introduction_of_conjunction", proposition(-2), proposition(-1));
			eapplyLast();
			eapplyLast();
			
			conclude();
		}
		
		rewriteRight(name(-1), name(-2));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn(final String targetName) {
		final List<Object> list = list(proposition(targetName));
		
		subdeduction();
		
		bind("definition_of_forall_in", list.get(1), list.get(3), list.get(4));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn2(final String targetName) {
		final List<Object> list = list(proposition(targetName));
		
		subdeduction();
		
		bind("definition_of_forall_in_2", list.get(1), list.get(3), list.get(5), list.get(6));
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
		eapplyLast();
		
		conclude();
	}
	
	public static final void deduceConjunctionRight(final String targetName) {
		final Object proposition = proposition(targetName);
		final Object left = left(proposition);
		final Object right = right(proposition);
		
		subdeduction();
		
		bind("right_elimination_of_conjunction", left, right);
		eapplyLast();
		
		conclude();
	}
	
	public static final void supposeEliminationOfParentheses() {
		final Object _X = $new("X");
		
		suppose("elimination_of_parentheses", $forall(_X,
				$(p(_X), "=", _X)));
	}
	
	public static final void supposeDefinitionOfSubset() {
		final Object _x = $new("x");
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("definition_of_subset", $forall(_X, $(FORALL, _Y, IN, U,
				$($(_X, SUBSET, _Y), "=", $forall(_x, $rule($(_x, IN, _X), $(_x, IN, _Y)))))));
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
	
	public static final void supposeDefinitionOfPowerset() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("definition_of_powerset", $forall(_X, _Y,
				$($(_X, IN, pp(_Y)), "=", $(_X, SUBSET, _Y))));
	}
	
	public static final void supposeTypeOfPowersetOfReals() {
		suppose("type_of_P_R",
				$(pp(R), SUBSET, U));
	}
	
	public static final void supposeRealsInUhm() {
		suppose("reals_in_Uhm",
				$(R, IN, U));
	}
	
	public static final void supposeDefinitionOfForallIn() {
		final Object _x = $new("x");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in", $forall(_x, _X, _P,
				$($(FORALL, _x, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), _P)))));
	}
	
	public static final void supposeDefinitionOfForallIn2() {
		final Object _x = $new("x");
		final Object _y = $new("y");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in_2", $forall(_x, _y, _X, _P,
				$($(FORALL, _x, ",", _y, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), _P)))))));
	}
	
	public static final void supposeDefinitionOfForallIn3() {
		final Object _x = $new("x");
		final Object _y = $new("y");
		final Object _z = $new("z");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in_3", $forall(_x, _y, _X, _P,
				$($(FORALL, _x, ",", _y, ",", _z, IN, _X, _P),
						"=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), $forall(_z, $rule($(_z, IN, _X), _P)))))))));
	}
	
	public static final void supposeDefinitionOfPositives() {
		final Object _n = $new("n");
		
		suppose("definition_of_positives", $forall(_n,
				$($(_n, IN, POS), "=", $($(_n, IN, N), LAND, $(0, "<", _n)))));
	}
	
	public static final void supposeIntroductionOfConjunction() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("introduction_of_conjunction",
				$forall(_X, _Y,
						$rule(_X, _Y, $(_X, LAND, _Y))));
	}
	
	public static final void supposeLeftEliminationOfConjunction() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("left_elimination_of_conjunction",
				$forall(_X, _Y,
						$rule($(_X, LAND, _Y), _X)));
	}
	
	public static final void supposeRightEliminationOfConjunction() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("right_elimination_of_conjunction",
				$forall(_X, _Y,
						$rule($(_X, LAND, _Y), _Y)));
	}
	
	public static final void supposeDefinitionOfLogicalEquivalence() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("definition_of_logical_equivalence",
				$forall(_X, _Y,
						$($(_X, EQUIV, _Y), "=", $($rule(_X, _Y), LAND, $rule(_Y, _X)))));
	}
	
	public static final void supposeLogicalEquality() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("logical_equality",
				$forall(_X, _Y,
						$rule($rule(_X, _Y), $($rule(_Y, _X)), $(_X, "=", _Y))));
	}
	
	public static final void deduceLogicalEquivalenceImpliesLogicalEquality() {
		subdeduction("logical_equivalence_implies_logical_equality");
		
		final Object _X = forall("X");
		final Object _Y = forall("Y");
		
		suppose($(_X, EQUIV, _Y));
		bind("definition_of_logical_equivalence", _X, _Y);
		rewrite(name(-2), name(-1));
		
		breakConjunction(name(-1));
		
		ebindTrim("logical_equality", _X, _Y);
		
		conclude();
	}
	
	public static final void deduceCommutativityOfConjunction() {
		subdeduction("commutativity_of_conjunction");
		
		final Object _X = forall("X");
		final Object _Y = forall("Y");
		
		{
			subdeduction();
			
			suppose($(_X, LAND, _Y));
			breakConjunction(name(-1));
			
			ebindTrim("introduction_of_conjunction", _Y, _X);
			
			conclude();
		}
		
		{
			subdeduction();
			
			suppose($(_Y, LAND, _X));
			breakConjunction(name(-1));
			
			ebindTrim("introduction_of_conjunction", _X, _Y);
			
			conclude();
		}
		
		ebindTrim("logical_equality", $(_X, LAND, _Y), $(_Y, LAND, _X));
		
		conclude();
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
	
	public static final void supposeSubsetInUhm() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("subset_in_Uhm",
				$forall(_X,
						$(FORALL, _Y, IN, U,
								$rule($(_X, SUBSET, _Y), $(_X, IN, U)))));
	}
	
	public static final void deduceNaturalsInUhm() {
		subdeduction("naturals_in_Uhm");
		
		ebindTrim("subset_in_Uhm", N, R);
		
		conclude();
	}
	
	public static final void tryCasesIfNot(final Object condition, final Object value, final Object _y) {
		subdeduction();
		
		{
			subdeduction();
			
			bind("try_cases_if_not", value, _y, condition);

			// TODO autodetect required verification
			final Object formula = second(condition(proposition(-1)));
			
			debugPrint(formula);
			debugPrint(condition);
			
			verifyBasicNumericProposition(formula);
			
			abort();
//			evaluateStructuralFormula(formula);
			
			apply(name(-2), name(-1));
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void tryCasesIf(final Object condition, final Object value) {
		subdeduction();
		
		{
			subdeduction();
			
			bind("try_cases_if", value, condition);
			
			// TODO autodetect required verification
//			evaluateStructuralFormula(condition(proposition(-1)));
			
			abort();
			
			apply(name(-2), name(-1));
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void tryCasesIfStop(final Object condition, final Object value, final Object _y) {
		subdeduction();
		
		{
			subdeduction();
			
			bind("try_cases_if_stop", value, _y, condition);
			
			// TODO autodetect required verification
//			evaluateStructuralFormula(condition(proposition(-1)));
			abort();
			
			
			apply(name(-2), name(-1));
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void tryCasesOtherwise(final Object value) {
		subdeduction();
		
		bind("try_cases_otherwise", value);
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void deduceSingleType(final String targetName) {
		final Object proposition = proposition(targetName);
		
		subdeduction();
		
		{
			subdeduction();
			
			ebindTrim("type_of_single", right(proposition), left(proposition));
			
			conclude();
		}
		
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final Object sequence(final Object separator, final Object... elements) {
		if (elements.length <= 1) {
			return Arrays.asList(elements);
		}
		
		List<Object> result = Arrays.asList(separator, elements[elements.length - 1]);
		
		for (int i = elements.length - 2; 0 < i; --i) {
			result = Arrays.asList(separator, elements[i], result);
		}
		
		result = Arrays.asList(elements[0], result);
		
		return result;
	}
	
	public static final void simplifyBasicNumericExpression(final String targetName, final Object expression) {
		subdeduction();
		
		final Object simplified = BasicNumericVerification.Verifier.INSTANCE.apply(expression);
		
		verifyBasicNumericProposition($(expression, "=", simplified));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void testSequenceHead() {
		{
			subdeduction("sequence_head.test1");
			
			computeSequenceHead(sequence(",", 1, 2, 3));
			
			conclude();
		}
		
		{
			subdeduction("sequence_tail.test1");
			
			computeSequenceTail(",", sequence(",", 1, 2, 3));
			
			conclude();
		}
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
													app("repeat", _n, str("i"), 0,
															block(app("write", str("result"), app("read", str("i"), 0) , $("to_java", _X))))))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_real_to_java",
					$(FORALL, _x, IN, R,
							$($("to_java", _x), "=", _x)));
		}
		
		{
			{
				final Object _a = $new("a");
				final Object _n = $new("n");
				final Object _b = $new("b");
				final Object _i = $new("i");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _i));
				final Object instruction = app("allocate", _a, _n);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _i));
				
				suppose("meaning_of_allocate_0",
						$forall(_a, _n, _b, _i, _p,
								$rule($(LNOT, $(_a, "=", _b)), $(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _n = $new("n");
				final Object _i = $new("i");
				final Object _p = $new("p");
				
				final Object instruction = app("allocate", _a, _n);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_allocate_1",
						$forall(_a, _n, _i, _p,
								$rule($(_i, IN, $(N, "_", $("<", _n))),
										$(valueAfter, IN, R))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _b = $new("b");
				final Object _j = $new("j");
				final Object _x = $new("x");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _j));
				final Object instruction = app("write", _a, _i, _x);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _j));
				
				suppose("meaning_of_write_0",
						$forall(_a, _i, _b, _j, _x, _p,
								$rule($(LNOT, $(_a, "=", _b)),
										$(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _x = $new("x");
				final Object _p = $new("p");
				
				final Object valueBefore = instructions(_p, app("read", str(_a), _i));
				final Object instruction = app("write", _a, _i, _x);
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_write_1",
						$forall(_a, _i, _x, _p,
								$rule($(_x, IN, R),
										$(valueBefore, IN, R),
										$(valueAfter, "=", _x))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _b = $new("b");
				final Object _j = $new("j");
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				final Object valueBefore = instructions(_p, app("read", str(_b), _j));
				final Object instruction = app("repeat", 0, _a, _i, block(_q));
				final Object valueAfter = instructions(_p, instruction, app("read", str(_b), _j));
				
				suppose("meaning_of_repeat_0",
						$forall(_a, _i, _p, _q,
								$rule($($(LNOT, $(_a, "=", _b)), LOR, $(LNOT, $(_i, "=", _j))),
										$(valueBefore, "=", valueAfter))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _n = $new("n");
				final Object _p = $new("p");
				final Object _q = $new("q");
				
				final Object instruction = app("repeat", _n, _a, _i, block(_q));
				final Object valueAfter = instructions(_p, instruction, app("read", str(_a), _i));
				
				suppose("meaning_of_repeat_1",
						$forall(_a, _i, _n, _p, _q,
								$rule($($(_n, IN, N)), $(valueAfter, "=", _n))));
			}
			
			{
				final Object _a = $new("a");
				final Object _i = $new("i");
				final Object _n = $new("n");
				final Object _q = $new("q");
				
				final Object instruction = app("repeat", _n, _a, _i, block(_q));
				final Object instruction2 = app("repeat", $(_n, "-", 1), _a, _i, block(_q));
				
				suppose("meaning_of_repeat_2",
						$forall(_a, _i, _n, _q,
								$rule($($(_n, IN, POS)), $(instruction, "=", $("sequence_concatenate", ";", $1(instruction2), _q)))));
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
			final Object _j = $new("j");
			
			final Goal goal = Goal.deduce("proof_of_to_java.test1",
					$forall(_n, $rule(
							$(_n, IN, POS),
							$forall(_p, $rule($($("to_java", $(p(_X), "_", $(_i, "<", _n))), "=", _p),
									$(instructions(_p, app("read", _r, _j)), "=", $(_X, "|", $1($(_i, "=", _j)), "@", $())))))));
			
			goal.introduce();
			
			final Object _m = $new("m");
			
			bind("induction_principle", $(conclusion(goal.getProposition()), "|", $1($(_n, "=", $(1, "+", _m))), "@", $()), _m);
			
			{
				final Goal subgoal = Goal.deduce(condition(proposition(-1)));
				
				{
					subdeduction();
					
					{
						subdeduction();
						
						substitute(target(subgoal.getProposition()), map(_m, 0));
						
						verifyBasicNumericProposition($($(1, "+", 0), "=", 1));
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					substitute(target(right(proposition(-1))), map(_n, 1));
					rewrite(name(-2), name(-1));
					
					substitute(1, map(_i, _j));
					rewrite(name(-2), name(-1), 1);
					
					conclude();
				}
				
				{
					final Goal subsubgoal = Goal.deduce(right(proposition(-1)));
					
					subsubgoal.intros();
					
					{
						subdeduction();
						
						new ToJavaHelper().compute(left(proposition(-1)));
						rewrite(name(-1), name(-2));
						
						conclude();
					}
					
					abort();
					
					subsubgoal.conclude();
				}
				
				
				subgoal.conclude();
			}
			
			abort();
			
//			goal.intros();
//			
//			{
//				subdeduction();
//				
//				bind("definition_of_positives", _n);
//				
//				rewrite(name(-3), name(-1));
//				
//				deduceConjunctionLeft(name(-1));
//				
//				conclude();
//			}
//			
//			{
//				subdeduction();
//				
//				new ToJavaHelper().compute(left(proposition(-2)));
//				
//				rewrite(name(-1), name(-3));
//				
//				conclude();
//			}
//			
//			abort();
			
			goal.conclude();
		}
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
	
	public static void supposeEliminationsOfCases() {
		{
			final Object _x = $new("x");
			
			suppose("try_cases_otherwise",
					$forall(_x,
							$(cases($(_x, "otherwise")), "=", _x)));
		}
		
		{
			final Object _x = $new("x");
			final Object _c = $new("c");
			
			suppose("try_cases_if",
					$forall(_x, _c,
							$rule(_c, $(cases($(_x, "if", _c)), "=", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _c = $new("c");
			
			suppose("try_cases_if_stop",
					$forall(_x, _y, _c,
							$rule(_c,
									$($("cases", $("", $(_x, "if", _c), _y)), "=", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _c = $new("c");
			
			suppose("try_cases_if_not",
					$forall(_x, _y, _c,
							$rule($(LNOT, _c),
									$($("cases", $("", $(_x, "if", _c), _y)), "=", $("cases", _y)))));
		}
	}

	public static void testEliminationOfCases() {
		{
			subdeduction("try_cases.test1");
			
			final Object _x = forall("x");
			
			suppose($(_x, "=", cases(
					$(42, "if", $(2, "=", 2)),
					$(24, "otherwise"))));
			
			{
				subdeduction();
				
				bind("try_cases_if_stop", 42, $("", $(24, "otherwise")), $(2, "=", 2));
				verifyBasicNumericProposition($(2, "=", 2));
				apply(name(-2), name(-1));
				
				conclude();
			}
			
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("try_cases.test2");
			
			final Object _x = forall("x");
			
			suppose($(_x, "=", cases(
					$(42, "if", $(2, "=", 3)),
					$(24, "if", $(1, "=", 2)),
					$(0, "otherwise"))));
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_if_not", 42, $("", $(24, "if", $(1, "=", 2)), $("", $(0, "otherwise"))), $(2, "=", 3));
					verifyBasicNumericProposition($(2, "=", 3));
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_if_not", 24, $("", $(0, "otherwise")), $(1, "=", 2));
					verifyBasicNumericProposition($(1, "=", 2));
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_otherwise", 0);
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			conclude();
		}
	}
	
	/**
	 * @author codistmonk (creation 2016-08-19)
	 */
	public static final class CaseDescription implements Serializable {
		
		private final Map<String, Object> variables;
		
		private final List<Object> conditions;
		
		private final Object definition;
		
		public CaseDescription(final Map<String, Object> variables, final List<Object> conditions, final Object definition) {
			this.variables = variables;
			this.conditions = conditions;
			this.definition = definition;
		}
		
		public final Map<String, Object> getVariables() {
			return this.variables;
		}
		
		public final List<Object> getConditions() {
			return this.conditions;
		}
		
		public final Object getDefinition() {
			return this.definition;
		}
		
		public final CaseDescription instantiate() {
			return this.instantiate("");
		}
		
		@SuppressWarnings("unchecked")
		public final CaseDescription instantiate(final String variableNamePostfix) {
			final Map<Variable, Object> map = new LinkedHashMap<>();
			final Map<String, Object> newVariables = new LinkedHashMap<>();
			
			for (final Map.Entry<String, ?> entry : this.getVariables().entrySet()) {
				final String newName = entry.getKey() + variableNamePostfix;
				final Object newValue = $new(newName);
				
				map.put((Variable) entry.getValue(), newValue);
				newVariables.put(newName, newValue);
			}
			
			return new CaseDescription(newVariables,
					(List<Object>) Variable.rewrite(this.getConditions(), map), Variable.rewrite(this.getDefinition(), map));
		}
		
		private static final long serialVersionUID = -9131355470296079371L;
		
	}
	
	public static final CaseDescription newSequenceAppendCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $()));
		final Object value = $1(_y);
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceAppendCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $1(_x0)));
		final Object value = $(_x0, $(_s, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceAppendCase2() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $(_x0, _x1)));
		final Object value = $(_x0, $("sequence_subappend", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubappendCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $(_s, _x0)));
		final Object value = $(_s, _x0, $(_s, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y),
				conditions,
				$($("sequence_subappend", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubappendCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $(_s, _x0, _x1)));
		final Object value = $(_s, _x0, $("sequence_subappend", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_subappend", _s, _x, _y), "=", value));
	}
	
	public static final void supposeDefinitionsForSequenceAppend() {
		/*
		 * 
		 * append s [] y      = [y]
		 * append s [x0] y    = [x0 [s y]]
		 * append s [x0 x1] y = [x0 (subappend s x1 y)]
		 * 
		 * subappend s [s x0] y    = [s x0 [s y]]
		 * subappend s [s x0 x1] y = [s x0 (subappend s x1 y)]
		 * 
		 */
		
		supposeDefinitions("sequence_append",
				newSequenceAppendCase0(),
				newSequenceAppendCase1(),
				newSequenceAppendCase2());
		
		supposeDefinitions("sequence_subappend",
				newSequenceSubappendCase0(),
				newSequenceSubappendCase1());
	}
	
	public static final void computeSequenceAppend(final Object s, final Object x, final Object y) {
		computeSequenceAppend(newName(), s, x, y);
	}
	
	public static final void computeSequenceAppend(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceAppendCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_append_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceAppendCase1();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_append_1", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceAppendCase2();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				{
					subdeduction();
					
					final Object[] values = v.values().stream().map(m::get).toArray();
					
					ebindTrim("definition_of_sequence_append_2", values);
					
					computeSequenceSubappend(s, values[3], y);
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $1($(x, "=", x)), y));
			
			conclude();
		}
	}
	
	public static final void computeSequenceSubappend(final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceSubappendCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_subappend_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceSubappendCase1();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				{
					subdeduction();
					
					final Object[] values = v.values().stream().map(m::get).toArray();
					
					ebindTrim("definition_of_sequence_subappend_1", values);
					
					computeSequenceSubappend(s, values[3], y);
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		rules.applyTo($(s, $1($(x, "=", x)), y));
	}
	
	public static final void supposeDefinitions(final String definedName, final CaseDescription... descriptions) {
		final int n = descriptions.length;
		
		for (int i = 0; i < n; ++i) {
			final CaseDescription caseDescription = descriptions[i].instantiate();
			
			suppose("definition_of_" + definedName + "_" + i,
					$forall(append(caseDescription.getVariables().values().toArray(),
							$rule(append(caseDescription.getConditions().toArray(), caseDescription.getDefinition())))));
		}
		
		for (int i = 0; i < n; ++i) {
			{
				final CaseDescription cI = descriptions[i].instantiate("_i");
				final CaseDescription cJ = descriptions[i].instantiate("_j");
				final Object[] variablesI = cI.getVariables().values().toArray();
				final Object[] variablesJ = cJ.getVariables().values().toArray();
				
				for (int k = 0; k < variablesI.length; ++k) {
					suppose("definition_of_" + definedName + "_inequality_" + i + "_" + i + "_" + k,
							$forall(append(cI.getVariables().values().toArray(),
									$rule(append(cI.getConditions().toArray(),
											$forall(append(cJ.getVariables().values().toArray(),
													$rule(append(cJ.getConditions().toArray(),
															$(LNOT, $(variablesI[k], "=", variablesJ[k])),
															$(LNOT, $(left(cI.getDefinition()), "=", left(cJ.getDefinition()))))))))))));
				}
			}
			
			for (int j = i + 1; j < n; ++j) {
				final CaseDescription cI = descriptions[i].instantiate("_i");
				final CaseDescription cJ = descriptions[j].instantiate("_j");
				
				suppose("definition_of_" + definedName + "_inequality_" + i + "_" + j,
						$forall(append(cI.getVariables().values().toArray(),
								$rule(append(cI.getConditions().toArray(),
										$forall(append(cJ.getVariables().values().toArray(),
												$rule(append(cJ.getConditions().toArray(),
														$(LNOT, $(left(cI.getDefinition()), "=", left(cJ.getDefinition()))))))))))));
			}
		}
	}
	
	public static final void testSequenceAppend() {
		final Object _s = $(",");
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = 2;
			
			computeSequenceAppend("sequence_append.test1", _s, _x, _y);
		}
		
		{
			final Object _x = sequence(_s, 1, 2);
			final Object _y = 3;
			
			computeSequenceAppend("sequence_append.test2", _s, _x, _y);
		}
		
		{
			final Object _x = sequence(_s, 1, 2, 3);
			final Object _y = 4;
			
			computeSequenceAppend("sequence_append.test3", _s, _x, _y);
		}
	}
	
	public static final CaseDescription newSequenceConcatenateCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $()));
		final Object value = _y;
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_y, "=", $()));
		final Object value = _x;
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase2() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		
		final List<Object> conditions = Arrays.asList($(_y, "=", $1(_y0)));
		final Object value = $("sequence_append", _s, _x, _y0);
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y,
						"y0", _y0),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase3() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $1(_x0)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_x0, $(_s, _y0, _y1));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase4() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_x0, _x1)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_x0, $("sequence_subconcatenate", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubconcatenateCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_s, _x0)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_s, _x0, $(_s, _y0, _y1));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_subconcatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubconcatenateCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_s, _x0, _x1)));
		final Object value = $(_s, _x0, $("sequence_subconcatenate", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_subconcatenate", _s, _x, _y), "=", value));
	}
	
	public static final void supposeDefinitionsForSequenceConcatenate() {
		/*
		 * 
		 * 0: concatenate s [] y            = y
		 * 1: concatenate s x []            = x
		 * 2: concatenate s x [y0]          = append s x y0
		 * 3: concatenate s [x0] [y0 y1]    = [x0 [s y0 y1]]
		 * 4: concatenate s [x0 x1] [y0 y1] = [x0 (subconcatenate s x1 y)]
		 * 
		 * 0: subconcatenate s [s x0] [y0 y1] = [s x0 [s y0 y1]] 
		 * 1: subconcatenate s [s x0 x1] y = [s x0 (subconcatenate s x1 y)] 
		 * 
		 */
		
		supposeDefinitions("sequence_concatenate",
				newSequenceConcatenateCase0(),
				newSequenceConcatenateCase1(),
				newSequenceConcatenateCase2(),
				newSequenceConcatenateCase3(),
				newSequenceConcatenateCase4());
		
		supposeDefinitions("sequence_subconcatenate",
				newSequenceSubconcatenateCase0(),
				newSequenceSubconcatenateCase1());
	}
	
	public static final void testSequenceConcatenate() {
		final Object _s = $(",");
		
		{
			final Object _x = sequence(_s);
			final Object _y = sequence(_s);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test1",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s);
			final Object _y = sequence(_s, 1);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test2",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = sequence(_s);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test3",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = sequence(_s, 2);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test4",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1, 2);
			final Object _y = sequence(_s, 3);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test5",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1, 2, 3);
			final Object _y = sequence(_s, 4, 5, 6);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.deduce("sequence_concatenate.test6",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
	}
	
	public static final void computeSequenceConcatenate(final Object s, final Object x, final Object y) {
		computeSequenceConcatenate(newName(), s, x, y);
	}
	
	public static final void computeSequenceConcatenate(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceConcatenateCase0();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), $(_y, "=", _y)), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase1();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x = v.get("x");
			
			rules.add(rule($(_s, $(_x, "=", _x), first(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_1", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase2();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x = v.get("x");
			final Object _y0 = v.get("y0");
			
			rules.add(rule($(_s, $(_x, "=", _x), first(c.getConditions())), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_concatenate_2", v.values().stream().map(m::get).toArray());
					computeSequenceAppend(m.get(_s), m.get(_x), m.get(_y0));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase3();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_3", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase4();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x1 = v.get("x1");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_concatenate_4", v.values().stream().map(m::get).toArray());
					computeSequenceSubconcatenate(m.get(_s), m.get(_x1), m.get(_y));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $(x, "=", x), $(y, "=", y)));
			
			conclude();
		}
	}
	
	public static final void computeSequenceSubconcatenate(final Object s, final Object x, final Object y) {
		computeSequenceSubconcatenate(newName(), s, x, y);
	}
	
	public static final void computeSequenceSubconcatenate(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceSubconcatenateCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_subconcatenate_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceSubconcatenateCase1();
			final Map<String, Object> v = c.getVariables();
			final Object _s = v.get("s");
			final Object _x1 = v.get("x1");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), $(_y, "=", _y)), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_subconcatenate_1", v.values().stream().map(m::get).toArray());
					computeSequenceSubconcatenate(m.get(_s), m.get(_x1), m.get(_y));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $(x, "=", x), $(y, "=", y)));
			
			conclude();
		}
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
				
				verifyBasicNumericProposition($(1, IN, N));
				
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
	
	public static final void supposeDefinitionsForSequenceHead() {
		{
			final Object _x0 = $new("x0");
			
			suppose("definition_of_sequence_head_1",
					$forall(_x0,
							$($("sequence_head", $1(_x0)), "=", _x0)));
		}
		
		{
			final Object _x0 = $new("x0");
			final Object _x1 = $new("x1");
			
			suppose("definition_of_sequence_head_2",
					$forall(_x0, _x1,
							$($("sequence_head", $(_x0, _x1)), "=", _x0)));
		}
	}
	
	public static final void supposeDefinitonsForSequenceTail() {
		{
			final Object _s = $new("s");
			final Object _x0 = $new("x0");
			final Object _x1 = $new("x1");
			
			suppose("definition_of_sequence_tail_1",
					$forall(_s, _x0, _x1,
							$($("sequence_tail", _s, $(_x0, $(_s, _x1))), "=", $1(_x1))));
		}
		
		{
			final Object _s = $new("s");
			final Object _x0 = $new("x0");
			final Object _x1 = $new("x1");
			final Object _x2 = $new("x2");
			
			suppose("definition_of_sequence_tail_2",
					$forall(_s, _x0, _x1, _x2,
							$($("sequence_tail", _s, $(_x0, $(_s, _x1, _x2))), "=", $(_x1, _x2))));
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
	
	public static final void eapplyLast() {
		eapply(name(-1));
	}
	
	public static final void eapply(final String targetName) {
		subdeduction();
				
		final String justificationName = justicationFor(condition(proposition(targetName))).getName();
		
		apply(targetName, justificationName);
		
		conclude();
	}
	
	public static final PropositionDescription justicationFor(final Object proposition) {
		PropositionDescription result = null;
		
		for (final PropositionDescription description : iterateBackward(deduction())) {
			if (new Substitution.ExpressionEquality().apply(proposition, description.getProposition())) {
				result = description;
				break;
			}
		}
		
		if (result == null) {
			if (isIdentity(proposition)) {
				bind("identity", left(proposition));
			} else if (isPositivity(proposition)) {
				deducePositivity(left(proposition));
			} else if(isNaturality(proposition) || isReality(proposition)) {
				verifyBasicNumericProposition(proposition);
			} else if(isCartesianProductity(proposition)) {
				deduceCartesianProduct(left(right(proposition)), flattenSequence(",", left(proposition)).toArray());
			} else {
				throw new IllegalStateException("Failed to justify: " + proposition);
			}
			
			result = new PropositionDescription()
			.setIndex(-1)
			.setName(name(-1))
			.setProposition(proposition(-1));
		}
		
		return result;
	}
	
	public static final boolean isIdentity(final Object expression) {
		final List<?> list = cast(List.class, expression);
		
		return 3 == list.size() && "=".equals(operator(expression)) && left(expression).equals(right(expression));
	}
	
	public static final void ebindLast(final Object... values) {
		ebind(name(-1), values);
	}
	
	public static final void ebindTrim(final String target, final Object... values) {
		subdeduction();
		
		ebind(target, values);
		trimLast();
		
		conclude();
	}
	
	public static final void ebind(final String target, final Object... values) {
		subdeduction();
		
		String newTarget = target;
		
		for (final Object value : values) {
			ebind1(newTarget, value);
			newTarget = name(-1);
		}
		
		conclude();
	}
	
	public static final void ebind1(final String target, final Object value) {
		subdeduction();
		
		String newTarget = target;
		boolean done = false;
		
		while (!done) {
//		while (!isBlock(proposition(newTarget))) {
//			debugPrint(proposition(newTarget));
			
			done = true;
			
			if (isForallIn(proposition(newTarget))) {
				canonicalizeForallIn(newTarget);
				newTarget = name(-1);
				done = false;
			} else if (isForallIn2(proposition(newTarget))) {
				canonicalizeForallIn2(newTarget);
				newTarget = name(-1);
				done = false;
			} else if (trim(newTarget)) {
				newTarget = name(-1);
				done = false;
			}
		}
		
		bind(newTarget, value);
		
		conclude();
	}
	
	public static final void trimLast() {
		trim(name(-1));
	}
	
	public static final boolean trim(final String target) {
		if (isRule(proposition(target))) {
			String newTarget = target;
			
			subdeduction();
			
			while (isRule(proposition(newTarget))) {
				eapply(newTarget);
				newTarget = name(-1);
			}
			
			conclude();
			
			return true;
		}
		
		return false;
	}
	
	public static final boolean isCartesianProductity(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		if (list != null && 3 == list.size() && IN.equals(middle(list))) {
			final List<?> type = cast(List.class, right(list));
			
			return type != null && "^".equals(middle(type));
		}
		
		return false;
	}
	
	public static final boolean isPositivity(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && POS.equals(right(list));
	}
	
	public static final boolean isNaturality(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && N.equals(right(list));
	}
	
	public static final boolean isReality(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && R.equals(right(list));
	}
	
	public static final boolean isForallIn(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 5 == list.size()
				&& FORALL.equals(list.get(0)) && IN.equals(list.get(2));
	}
	
	public static final boolean isForallIn2(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 7 == list.size()
				&& FORALL.equals(list.get(0)) && ",".equals(list.get(2)) && IN.equals(list.get(4));
	}
	
	public static final Iterable<PropositionDescription> iterateBackward(final Deduction deduction) {
		return new Iterable<Computation.PropositionDescription>() {
			
			@Override
			public final Iterator<PropositionDescription> iterator() {
				return new Iterator<Computation.PropositionDescription>() {
					
					private final PropositionDescription result = new PropositionDescription();
					
					private Deduction currentDeduction = deduction;
					
					private int i = this.currentDeduction.getPropositionNames().size();
					
					@Override
					public final boolean hasNext() {
						return 0 < this.i || !isEmpty(this.currentDeduction.getParent());
					}
					
					@Override
					public final PropositionDescription next() {
						if (--this.i < 0) {
							this.currentDeduction = this.currentDeduction.getParent();
							
							while (this.currentDeduction.getPropositionNames().isEmpty()) {
								this.currentDeduction = this.currentDeduction.getParent();
							}
							
							this.i = this.currentDeduction.getPropositionNames().size() - 1;
						}
						
						final String name = this.currentDeduction.getPropositionNames().get(this.i);
						
						return this.result
								.setIndex(this.result.getIndex() - 1)
								.setName(name)
								.setProposition(this.currentDeduction.getPropositions().get(name));
					}
					
				};
			}
			
		};
	}
	
	public static final boolean isEmpty(final Deduction deduction) {
		return deduction == null
				|| (deduction.getPropositionNames().isEmpty()
						&& (deduction.getParent() == null || isEmpty(deduction.getParent())));
	}
	
	public static final int[] toInts(final List<Object> numbers) {
		return numbers.stream().mapToInt(n -> ((Number) n).intValue()).toArray();
	}
	
	public static final List<Object> flattenSequence(final Object separator, final Object sequence) {
		final List<Object> result = new ArrayList<>();
		final List<?> list = list(sequence);
		
		if (list.isEmpty()) {
			return Collections.emptyList();
		}
		
		result.add(first(list));
		
		if (2 == list.size()) {
			List<?> tmp = list(second(list));
			
			while (tmp != null) {
				if (2 == tmp.size() && separator.equals(first(tmp))) {
					result.add(second(tmp));
					break;
				}
				
				if (3 == tmp.size() && separator.equals(first(tmp))) {
					result.add(second(tmp));
					tmp = list(tmp.get(2));
				}
			}
		} else if (1 != list.size()) {
			throw new IllegalArgumentException();
		}
		
		return result;
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
	 * @author codistmonk (creation 2016-08-12)
	 */
	public static final class PropositionDescription implements Serializable {
		
		private int index;
		
		private String name;
		
		private Object proposition;
		
		public final int getIndex() {
			return this.index;
		}
		
		public final PropositionDescription setIndex(final int index) {
			this.index = index;
			
			return this;
		}
		
		public final String getName() {
			return this.name;
		}
		
		public final PropositionDescription setName(final String name) {
			this.name = name;
			
			return this;
		}
		
		public final Object getProposition() {
			return this.proposition;
		}
		
		public final PropositionDescription setProposition(final Object proposition) {
			this.proposition = proposition;
			
			return this;
		}
		
		@Override
		public final String toString() {
			return this.getIndex() + ": " + this.getName() + ": " + this.getProposition();
		}
		
		private static final long serialVersionUID = -3590873676651429520L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-14)
	 */
	public static final class CasesHelper implements Serializable {
		
		private final List<Pair<Object, Object>> cases = new ArrayList<>();
		
		public final CasesHelper addCase(final Object value) {
			return this.addCase(value, null);
		}
		
		public final CasesHelper addCase(final Object value, final Object condition) {
			this.cases.add(new Pair<>(value, condition));
			
			return this;
		}
		
		public final void selectCase(final int index) {
			final int n = this.cases.size();
			final Object[] continuations = new Object[n];
			
			for (int i = n - 2; 0 <= i; --i) {
				final Pair<Object, Object> nextCase = this.cases.get(i + 1);
				final Object nextItem = nextCase.getSecond() == null
						? $(nextCase.getFirst(), "otherwise")
								: $(nextCase.getFirst(), "if", nextCase.getSecond());
				
				if (i == n - 2) {
					continuations[i] = $("", nextItem);
				} else {
					continuations[i] = $("", nextItem, continuations[i + 1]);
				}
			}
			
			for (int i = 0; i < index; ++i) {
				final Pair<Object, Object> c = this.cases.get(i);
				
				tryCasesIfNot(c.getSecond(), c.getFirst(), continuations[i]);
			}
			
			final Pair<Object, Object> c = this.cases.get(index);
			
			if (c.getSecond() == null) {
				tryCasesOtherwise(c.getFirst());
			} else if (continuations[index] == null) {
				tryCasesIf(c.getSecond(), c.getFirst());
			} else {
				tryCasesIfStop(c.getSecond(), c.getFirst(), continuations[index]);
			}
		}
		
		private static final long serialVersionUID = -598430379891995844L;
		
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
					verifyBasicNumericProposition($($(this.n, "-", 1), "=", this.n - 1));
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
						
						this.rules.applyTo($("to_java", _X));
						
						rewrite(name(-2), name(-1));
						
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
