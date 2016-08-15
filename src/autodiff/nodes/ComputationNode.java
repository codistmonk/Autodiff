package autodiff.nodes;

import static autodiff.reasoning.deductions.Standard.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.*;
import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.Deduction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Pair;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class ComputationNode extends AbstractNode<ComputationNode> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private final List<BindListener> bindListeners;
	
	private String typeName;
	
	private Runnable binder;
	
	private Deduction boundForm;
	
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
	
	public final Runnable getBinder() {
		return this.binder;
	}
	
	public final ComputationNode setBinder(final Runnable binder) {
		this.binder = binder;
		
		return this;
	}
	
	@Override
	public final String getName() {
		return "[" + this.getId() + "]" + this.getTypeName();
	}
	
	@Override
	public final ComputationNode autoShape() {
		final Deduction deduction = this.getBoundForm();
		final Object proposition = deduction.getProposition(deduction.getPropositionName(-1));
//		final Object shapeExpression = middle(right(middle(right(proposition))));
		final Object shapeExpression = right(middle(right(proposition)));
		
		setShape(flattenBinaryTree(shapeExpression).stream().mapToInt(
				o -> ((Number) o).intValue()).toArray());
		
		return this;
	}
	
	public final Deduction getBoundForm() {
		if (this.boundForm == null) {
			this.boundForm = Standard.build(new Deduction(
					AUTODIFF, this.getName() + "_bind"), this.getBinder(), 1);
		}
		
		return this.boundForm;
	}
	
	public static final void eapplyLast() {
		eapply(name(-1));
	}
	
	public static final void eapply(final String target) {
		subdeduction();
		
		final Object condition = condition(proposition(target));
		
		PropositionDescription justification = null;
		
		for (final PropositionDescription description : iterateBackward(deduction())) {
			if (condition.equals(description.getProposition())) {
				justification = description;
				break;
			}
		}
		
		final String justificationName;
		
		if (justification == null) {
			if (isPositivity(condition)) {
				deducePositivity(left(condition));
			} else if(isNaturality(condition) || isReality(condition)) {
				verifyBasicNumericProposition(condition);
			} else {
				throw new IllegalStateException();
			}
			justificationName = name(-1);
		} else {
			justificationName = justification.getName();
		}
		
		apply(target, justificationName);
		
		conclude();
	}
	
	public static final void ebindLast(final Object... values) {
		ebind(name(-1), values);
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
		return new Iterable<ComputationNode.PropositionDescription>() {
			
			@Override
			public final Iterator<PropositionDescription> iterator() {
				return new Iterator<ComputationNode.PropositionDescription>() {
					
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
	
	public static final SequenceBuilder SB_COMMA = new SequenceBuilder(",");
	
	public static final SequenceBuilder SB_CROSS = new SequenceBuilder(CROSS);
	
	public static final Object cases(final Object... cases) {
		return new SequenceBuilder("").build(append(array((Object) "cases"), cases));
	}
	
	public static final Deduction AUTODIFF = Standard.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Standard.setup();
			
			debugPrint(SB_COMMA.build($(1, 2, 3)));
			debugPrint(SB_COMMA.build(1));
			debugPrint(SB_COMMA.build(1, 2));
			debugPrint(SB_COMMA.build(1, 2, 3));
			debugPrint(SB_COMMA.build(1, SB_COMMA.build(2, 3)));
			debugPrint(SB_COMMA.build(SB_COMMA.build(1, 2), 3));
			
			supposeDefinitionOfParentheses();
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
			
			{
				final Object _i = $new("i");
				final Object _n = $new("n");
				
				suppose("definition_of_range",
						$(FORALL, _n, IN, N,
								$forall(_i,
										$($(_i, IN, $(N, "_", $("<", _n))),
												"=", $($(_i, IN, N), LAND, $(_i, "<", _n))))));
			}
			
			{
				final Object _i = $new("i");
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _X = $new("X");
				
				suppose("definition_of_indexing_i",
						$(FORALL, _i, IN, POS,
									$rule($(p(_x, ",", _y), IN, $($(_X, "^", _i), CROSS, _X)),
											$($(p(_x, ",", _y), "_", _i), "=", _y))));
			}
			
			supposeTransitivityOfSubset();
			deducePositivesSubsetNaturals();
			deducePositivesInUhm();
			supposeDefinitionOfMs();
			supposeTypeOfFlat();
			supposeDefinitionOfSingleton();
			supposeTypeOfSingle();
//			supposeTypeOfPair();
			supposeCartesian1();
			supposeTypeOfCartesian();
			supposeCartesianMN();
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("type_of_tuple",
						$(FORALL, _X, ",", _Y, IN, U,
								$(FORALL, _x, IN, _X,
										$(FORALL, _y, IN, _Y,
												$(SB_COMMA.build(_x, _y), IN, SB_CROSS.build(_X, _Y))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _n = $new("n");
				
				suppose("vector_type_in_Uhm",
						
						$(FORALL, _X, IN, U,
								$(FORALL, _n, IN, N,
										$($(_X, "^", _n), IN, U))));
			}
			
			{
				final Object _s = $new("s");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("definition_of_sequence_new",
						$forall(_s, _x, _y,
								$($("sequence_new", _s, _x, _y), "=", $(_x, $(_s, _y)))));
			}
			
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
			
			{
				final Object _s = $new("s");
				final Object _x = $new("x");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				final Object _y = $new("y");
				
				// TODO use $(_s, _x1) instead of _x1
				final Object condition0 = $(_x, ":=:", $(_x0, _x1));
				final Object value0 = $(_x0, $("sequence_append", _s, _x1, _y));
				
				final Object condition1 = $(_x, ":=:", $(_s, _x0));
				final Object value1 = $(_s, _x0, $(_s, _y));
				
				final Object condition2 = $(_x, ":=:", $(_s, _x0, _x1));
				final Object value2 = $(_s, _x0, $("sequence_append", _s, _x1, _y));
				
				final Object condition3 = $(_x, ":=:", $1(_x0));
				final Object value3 = $(_x0, $(_s, _y));
				
				suppose("definition_of_sequence_append",
						$forall(_s, _x, _x0, _x1, _y,
								$($("sequence_append", _s, _x, _y), "=", cases(
										$(value0, "if", condition0),
										$(value1, "if", condition1),
										$(value2, "if", condition2),
										$(value3, "if", condition3)))));
			}
			
			{
				final Object _s = ",";
				final Object _x = $1(1);
				final Object _y = 2;
				
				new SequenceAppendHelper(_s, _x, _y).compute("sequence_append.test1");
			}
			
			{
				final Object _s = ",";
				final Object _x = SB_COMMA.build(1, 2);
				final Object _y = 3;
				
				new SequenceAppendHelper(_s, _x, _y).compute("sequence_append.test2");
			}
			
			{
				final Object _s = ",";
				final Object _x = SB_COMMA.build(1, 2, 3);
				final Object _y = 4;
				
				new SequenceAppendHelper(_s, _x, _y).compute("sequence_append.test3");
			}
			
			{
				final Object _X = $new("X");
				final Object _x = $new("x");
				
				suppose("type_of_single2",
						$(FORALL, _X, IN, U,
								$forall(_x,
										$($(_x, IN, _X), "=", $($1(_x), IN, $1(_X))))));
			}
			
			{
				final Object _X = $new("X");
				
				suppose("type_of_single_in_Uhm",
						$(FORALL, _X, IN, U,
								$($1(_X), IN, U)));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("type_of_tuple2",
						$(FORALL, _X, ",", _Y, IN, U,
								$(FORALL, _x, IN, _X,
										$(FORALL, _y, IN, _Y,
												$($("sequence_append", ",", _x, _y), IN, $("sequence_append", CROSS, _X, _Y))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("tuple_type_in_Uhm",
						$(FORALL, _X, ",", _Y, IN, U,
								$($("sequence_append", CROSS, _X, _Y), IN, U)));
			}
			
			{
				subdeduction("single_N_in_Uhm");
				
				ebind("type_of_single_in_Uhm", N);
				trimLast();
				
				conclude();
			}
			
			{
				subdeduction("type_of_tuple2.test1");
				
				{
					subdeduction();
					
					verifyBasicNumericProposition($(1, IN, N));
					
					{
						subdeduction();
						
						ebind("type_of_single2", N, 1);
						trimLast();
						
						conclude();
					}
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				{
					subdeduction();
					
					ebind("type_of_tuple2", $1(N), N, $1(1), 2);
					trimLast();
					
					conclude();
				}
				
				final List<?> _x = list(left(proposition(-1)));
				final List<?> _X = list(right(proposition(-1)));
				
				debugPrint(_x);
				debugPrint(_X);
				
				new SequenceAppendHelper(_x.get(1), _x.get(2), _x.get(3)).compute();
				rewrite(name(-2), name(-1));
				
				new SequenceAppendHelper(_X.get(1), _X.get(2), _X.get(3)).compute();
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction("type_of_tuple2.test2");
				
				{
					subdeduction();
					
					ebind("tuple_type_in_Uhm", $1(N), N);
					trimLast();
					
					new SequenceAppendHelper(CROSS, $1(N), N).compute();
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				{
					subdeduction();
					
					ebind("type_of_tuple2", SB_CROSS.build(N, N), N, SB_COMMA.build(1, 2), 3);
					trimLast();
					
					conclude();
				}
				
				final List<?> _x = list(left(proposition(-1)));
				final List<?> _X = list(right(proposition(-1)));
				
				new SequenceAppendHelper(_x.get(1), _x.get(2), _x.get(3)).compute();
				rewrite(name(-2), name(-1));
				
				new SequenceAppendHelper(_X.get(1), _X.get(2), _X.get(3)).compute();
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				final Object _s = $new("s");
				final Object _x = $new("x");
				
				suppose("definition_of_repeat_1",
						$forall(_s, _x,
								$($("repeat", _s, _x, 1), "=", $1(_x))));
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
			
			{
				final Object _n = $new("n");
				final Object _X = $new("X");
				
				suppose("simplification_of_tuple_type",
						$(FORALL, _X, IN, U,
								$(FORALL, _n, IN, N,
										$($("repeat", CROSS, _X, _n), "=", $(_X, "^", _n)))));
			}
			
			{
				subdeduction("simplification_of_tuple_type.test1");
				
				ebind("simplification_of_tuple_type", N, 3);
				trimLast();
				
				{
					subdeduction();
					
					{
						subdeduction();
						
						ebind("definition_of_repeat_n", CROSS, N, 3);
						trimLast();
						
						verifyBasicNumericProposition($($(3, "-", 1), "=", 2));
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					final List<?> rhs = list(right(proposition(-1)));
					
					debugPrint(rhs);
					
					{
						subdeduction();
						
						{
							subdeduction();
							
							ebind("definition_of_repeat_n", CROSS, N, 2);
							trimLast();
							
							verifyBasicNumericProposition($($(2, "-", 1), "=", 1));
							rewrite(name(-2), name(-1));
							
							conclude();
						}
						
						{
							subdeduction();
							
							ebind("definition_of_repeat_1", CROSS, N);
							trimLast();
							
							conclude();
						}
						
						rewrite(name(-2), name(-1));
						
						new SequenceAppendHelper(CROSS, $1(N), N).compute();
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					rewrite(name(-2), name(-1));
					
					new SequenceAppendHelper(CROSS, SB_CROSS.build(N, N), N).compute();
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction("type_of_tuple.test3");
				
				rewrite("type_of_tuple2.test2", "simplification_of_tuple_type.test1");
				
				conclude();
			}
			
			abort();
			
			{
				final Object _f = $new("f");
				final Object _x = $new("x0");
				final Object _sx = $new("sx");
				final Object _y = $new("y0");
				final Object _sy = $new("sy");
				
				suppose("definition_of_zip_0",
						$forall(_x, _sx, _y, _sy,
								$($("zip", _f, _sx, _sy, $(_sx, _x), $(_sy, _y)), "=", $(_f, _x, _y))));
			}
			
			{
				final Object _f = $new("f");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				final Object _sx = $new("sx");
				final Object _y0 = $new("y0");
				final Object _y1 = $new("y1");
				final Object _sy = $new("sy");
				
				suppose("definition_of_zip_n",
						$forall(_x0, _x1, _sx, _y0, _y1, _sy,
								$($("zip", _f, _sx, _sy, $(_sx, _x0, _x1), $(_sy, _y0, _y1)), "=", $($(_f, _x0, _y0), $("zip", _f, _sx, _sy, _x1, _y1)))));
			}
			
			{
				final Object _f = $new("f");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				final Object _sx = $new("sx");
				final Object _y0 = $new("y0");
				final Object _y1 = $new("y1");
				final Object _sy = $new("sy");
				
				suppose("definition_of_zip_begin",
						$forall(_x0, _x1, _sx, _y0, _y1, _sy,
								$($("zip", _f, _sx, _sy, $(_x0, $(_sx, _x1)), $(_y0, $(_sy, _y1))), "=", $($(_f, _x0, _y0), $("zip", _f, _sx, _sy, _x1, _y1)))));
			}
			
			{
				final Object _f = $new("f");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				
				suppose("definition_of_reduce_0",
						$forall(_f, _x0, _x0,
								$($("reduce", _f, $(_x0, _x1)), "=", $(_f, _x0, _x1))));
			}
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				
				suppose("definition_of_cross_type",
						$forall(_x, _X,
								$rule($("reduce", LAND, $("zip", IN, ",", CROSS, _x, _X)), $(_x, IN, _X))));
			}
			
			supposeDefinitionOfProductLoop0();
			supposeDefinitionOfProductLoopN();
			supposeDefinitionOfProductReduction();
		}
		
	}, 1);
	
	public static final ComputationNode ones() {
		final ComputationNode result = new ComputationNode().setTypeName("ones");
		
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
					
					ebindLast($(result.get("n")));
					eapplyLast();
					
					canonicalizeForallIn(name(-1));
					
					final Object[] s = toObjects((int[]) result.get("s"));
					
//					bind(name(-1), p(toBinaryTree(",", s)));
					bind(name(-1), SB_COMMA.build(s));
					
					deduceCartesianType(s, "positivity");
					
					apply(name(-2), name(-1));
					
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
	
	public static final void deduceCartesianPositivity(final Object value) {
		subdeduction();
		
		ebind("cartesian_1", POS);
		eapplyLast();
		deducePositivity(value);
		rewrite(name(-1), name(-2));
		
		conclude();
	}
	
	public static final void deduceCartesianRealness(final Object value) {
		subdeduction();
		
		ebind("cartesian_1", R);
		eapplyLast();
		verifyBasicNumericProposition($(value, IN, R));
		rewrite(name(-1), name(-2));
		
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
	
	public static final void supposeDefinitionOfParentheses() {
		final Object _X = $new("X");
		
		suppose("definition_of_parentheses", $forall(_X,
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
	
	public static final void supposeTransitivityOfSubset() {
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
				
				ebind("definition_of_subset", _X, _Y);
				trimLast();
				rewrite(h1, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), h3);
			
			{
				subdeduction();
				
				ebind("definition_of_subset", _Y, _Z);
				trimLast();
				rewrite(h2, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), name(-2));
			
			conclude();
		}
		
		ebind("definition_of_subset", _X, _Z);
		trimLast();
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
		
		bind("logical_equality", _X, _Y);
		trimLast();
		
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
			
			bind("introduction_of_conjunction", _Y, _X);
			trimLast();
			
			conclude();
		}
		
		{
			subdeduction();
			
			suppose($(_Y, LAND, _X));
			breakConjunction(name(-1));
			
			bind("introduction_of_conjunction", _X, _Y);
			trimLast();
			
			conclude();
		}
		
		bind("logical_equality", $(_X, LAND, _Y), $(_Y, LAND, _X));
		trimLast();
		
		conclude();
	}
	
	public static final void deducePositivesSubsetNaturals() {
		subdeduction("positives_subset_naturals");
		
		ebind("definition_of_subset", POS, N);
		trimLast();
		
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
	
	public static final void supposeTypeOfSingle() {
		final Object _X = $new("X");
		final Object _x = $new("x");
		
		suppose("type_of_single",
				$forall(_X,
						$(FORALL, _x, IN, _X,
										$(p(_x), IN, _X))));
	}
	
	public static final void supposeTypeOfPair() {
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
	
	public static final void supposeCartesian1() {
		final Object _X = $new("X");
		
		suppose("cartesian_1",
				$(FORALL, _X, IN, U,
						$(_X, "=", $(_X, "^", 1))));
	}
	
	public static final void supposeTypeOfCartesian() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("type_of_cartesian",
				$(FORALL, _X, ",", _Y, IN, U,
						$(pp(_X, CROSS, _Y), SUBSET, U)));
	}
	
	public static final void supposeCartesianMN() {
		final Object _X = $new("X");
		final Object _m = $new("m");
		final Object _n = $new("n");
		
		suppose("cartesian_m_n",
				$(FORALL, _X, IN, U,
						$(FORALL, _m, ",", _n, IN, POS,
								$(SB_CROSS.build($(_X, "^", _m), $(_X, "^", _n)), "=", SB_CROSS.build($(_X, "^", $(_m, "+", _n)))))));
	}
	
	public static final void deducePositivesInUhm() {
		subdeduction("positives_in_Uhm");
		
		ebind("subset_in_Uhm", POS, N);
		trimLast();
		
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
												"=", $($(PI, "_", $(_i, "<", $(_n, "-", 1)), _X), $(_X, "|", $(_i, "=", $(_n, "-", 1)))))))));
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
	
	public static final void deduceCartesianType(final Object[] s, final String type) {
		subdeduction();
		
		boolean first = true;
		
		for (final Object value : s) {
			if ("positivity".equals(type)) {
				deduceCartesianPositivity(value);
			} else {
				deduceCartesianRealness(value);
			}
			
			if (first) {
				first = false;
			} else {
				final Object x = left(proposition(-2));
				final Object y = left(proposition(-1));
				
				final Object m = right(right(proposition(-2)));
				final Object n = right(right(proposition(-1)));
				
				{
					subdeduction();
					
					{
						subdeduction();
						
						ebind("vector_type_in_Uhm", POS, m);
						trimLast();
						
						ebind("vector_type_in_Uhm", POS, n);
						trimLast();
						
						ebind("type_of_tuple",
								$(POS, "^", m), $(POS, "^", n), x, y);
						
						eapplyLast();
						
//						bind("definition_of_parentheses", middle(left(proposition(-1))));
//						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					{
						subdeduction();
						
						ebind("cartesian_m_n", POS, m, n);
						eapplyLast();
						
						verifyBasicNumericProposition(
								$($(m, "+", n), "=", (Integer) m + (Integer) n));
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
			}
		}
		
//		bind("definition_of_parentheses", left(proposition(-1)));
//		rewriteRight(name(-2), name(-1));
		
		conclude();
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
		
		ebind("subset_in_Uhm", N, R);
		trimLast();
		
		conclude();
	}
	
	public static final void tryCasesIfNot(final Object condition, final Object value, final Object _y) {
		subdeduction();
		
		{
			subdeduction();
			
			bind("try_cases_if_not", value, _y, condition);

			// TODO autodetect required verification
			evaluateStructuralFormula(second(condition(proposition(-1))));
			
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
			evaluateStructuralFormula(condition(proposition(-1)));
			
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
			evaluateStructuralFormula(condition(proposition(-1)));
			
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
	 * @author codistmonk (creation 2016-08-13)
	 */
	public static final class SequenceBuilder implements Serializable {
		
		private final Object separator;
		
		public SequenceBuilder(final Object separator) {
			this.separator = separator;
		}
		
		public final Object getSeparator() {
			return this.separator;
		}
		
		public final Object build(final Object... elements) {
			if (1 == elements.length) {
				return Arrays.asList(elements[0]);
			}
			
			List<Object> result = Arrays.asList(this.getSeparator(), elements[elements.length - 1]);
			
			for (int i = elements.length - 2; 0 < i; --i) {
				result = Arrays.asList(this.getSeparator(), elements[i], result);
			}
			
			result = Arrays.asList(elements[0], result);
			
			return result;
			
			/*
			 * 
			 * 1
			 * [( 1 )]
			 * [1]
			 * 
			 * 1,2
			 * [( 1 [, 2 )]
			 * [1 [, 2]]
			 * 
			 * 1,2,3
			 * [( 1 [, 2 [, 3 )]]]
			 * [1 [, 2 [, 3]]]
			 * 
			 * 		
			 * 
			 * 1,(2,3)
			 * [( 1 [, [( 2 [, 3 )]] )]]
			 * [1 [, [2 [, 3]]]]
			 * 
			 * (1,2),3
			 * [( [( 1 [, 2 )]] [, 3 )]]
			 * [[1 [, 2]] [, 3]]
			 * 
			 */
		}
		
		private static final long serialVersionUID = 4750503376771325114L;
		
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
	 * @author codistmonk (creation 2016-08-14)
	 */
	public static final class SequenceAppendHelper implements Serializable {
		
		private final Object s;
		
		private Object x;
		
		private Object x0;
		
		private Object x1;
		
		private final Object y;
		
		private Object condition0;
		
		private Object value0;
		
		private Object condition1;
		
		private Object value1;
		
		private Object condition2;
		
		private Object value2;
		
		private Object condition3;
		
		private Object value3;
		
		private boolean first;
		
		public SequenceAppendHelper(final Object s, final Object x, final Object y) {
			this(s, x, x0(s, x), x1(s, x), y);
		}
		
		public SequenceAppendHelper(final Object s, final Object x, final Object x0,
				final Object x1, final Object y) {
			this.s = s;
			this.x = x;
			this.x0 = x0;
			this.x1 = x1;
			this.y = y;
			this.first = true;
			
			this.setConditionsAndValues();
		}
		
		public final void compute() {
			this.compute(newName());
		}
		
		public final void compute(final String name) {
			subdeduction(name);
			
			int caseIndex;
			
			do {
				caseIndex = 3;
				final List<?> list = cast(List.class, this.x);
				
				if (list != null) {
					if (2 == list.size()) {
						if (this.s.equals(first(list))) {
							caseIndex = 1;
						} else {
							caseIndex = 0;
						}
					} else if (3 == list.size() && this.s.equals(first(list))) {
						caseIndex = 2;
					}
				}
				
				this.compute(caseIndex);
			} while (caseIndex != 1 && caseIndex != 3);
			
			conclude();
		}
		
		public final void compute(final int caseIndex) {
			subdeduction();
			
			bind("definition_of_sequence_append", this.s, this.x, this.x0, this.x1, this.y);
			
			debugPrint(caseIndex, this.s, this.x, this.x0, this.x1, this.y);
			
			new CasesHelper()
			.addCase(this.value0, this.condition0)
			.addCase(this.value1, this.condition1)
			.addCase(this.value2, this.condition2)
			.addCase(this.value3, this.condition3)
			.selectCase(caseIndex);
			
//			if (3 == caseIndex) {
//				subdeduction();
//				
//				bind("definition_of_sequence_new", this.s, this.x, this.y);
//				rewrite(name(-2), name(-1));
//				
//				conclude();
//			}
			
			conclude();
			
			if (this.first) {
				this.first = false;
			} else {
				rewrite(name(-2), name(-1));
			}
			
			if (caseIndex == 0 || caseIndex == 2) {
				this.x = this.x1;
				this.setX0X1();
				this.setConditionsAndValues();
			}
		}
		
		private final void setX0X1() {
			this.x0 = x0(this.s, this.x);
			this.x1 = x1(this.s, this.x);
		}
		
		private final void setConditionsAndValues() {
			this.condition0 = $(this.x, ":=:", $(this.x0, this.x1));
			this.value0 = $(this.x0, $("sequence_append", this.s, this.x1, this.y));
			
			this.condition1 = $(this.x, ":=:", $(this.s, this.x0));
			this.value1 = $(this.s, this.x0, $(this.s, this.y));
			
			this.condition2 = $(this.x, ":=:", $(this.s, this.x0, this.x1));
			this.value2 = $(this.s, this.x0, $("sequence_append", this.s, this.x1, this.y));
			
			this.condition3 = $(this.x, ":=:", $1(this.x0));
			this.value3 = $(this.x0, $(this.s, this.y));
		}
		
		private static final long serialVersionUID = 1480975513598301733L;
		
		public static final Object x0(final Object s, final Object x) {
			final List<?> list = cast(List.class, x);
			
			if (list == null) {
				return $("()");
			}
			
			if (1 == list.size()) {
				return first(list);
			}
			
			if (2 == list.size()) {
				if (s.equals(first(list))) {
					return second(list);
				}
				
				return first(list);
			}
			
			if (3 == list.size() && s.equals(first(list))) {
				return second(list);
			}
			
			throw new IllegalArgumentException();
		}
		
		public static final Object x1(final Object s, final Object x) {
			final List<?> list = cast(List.class, x);
			
			if (list == null || 1 == list.size()) {
				return $("()");
			}
			
			if (2 == list.size()) {
				return second(list);
			}
			
			if (3 == list.size() && s.equals(first(x))) {
				return list.get(2);
			}
			
			throw new IllegalArgumentException();
		}
		
	}
	
}
