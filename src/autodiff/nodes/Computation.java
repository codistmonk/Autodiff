package autodiff.nodes;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Propositions.*;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalize;
import static autodiff.reasoning.deductions.ScalarAlgebra.newElementarySimplificationRule;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.autoapply;
import static autodiff.reasoning.tactics.Auto.autoapplyOnce;
import static autodiff.reasoning.tactics.Auto.autobind;
import static autodiff.reasoning.tactics.Auto.autobindTrim;
import static autodiff.reasoning.tactics.Auto.autodeduce;
import static autodiff.reasoning.tactics.Auto.tryMatch;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.rules.Variable.matchOrFail;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.ScalarAlgebra;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Auto.Simplifier;

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
			
			supposeDefinitionsForJavaCode();
			supposeDefinitionsForCLCode();
		}
		
	}, new Simple(1));
	
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
						autobindTrim("definition_of_vector_reduction_by_product_1",
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
							
							autobindTrim("definition_of_vector_reduction_by_product_2",
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
									$rule($(FORALL, _j, IN, $(N, "_", $("<", _n)), $($(_X, "|", $1($replacement(_i, _j)), "@", $()), IN, R)),
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
										"=", instructions(_p, $(_f, "(", $(_x, "|", $1($replacement(app("read", str(_a), _i), valueAfterP)), "@", $()), ")")))));
			}
		}
		
		{
			final Object _P = $new("P");
			final Object _n = $new("n");
			
			suppose("induction_principle",
					$forall(_P, _n,
							$rule($(_P, "|", $1($replacement(_n, 0)), "@", $()),
									$(FORALL, _n, IN, N, $rule(_P, $(_P, "|", $1($replacement(_n, $(_n, "+", 1))), "@", $()))),
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
									$(instructions(_p, app("read", _r, _j)), "=", $(_X, "|", $1($replacement(_i, _j)), "@", $())))))));
			
			goal().introduce();
			
			final Object _m = $new("m");
			
			bind("full_induction", "induction_principle", $(conclusion(goal().getProposition()), "|", $1($replacement(_n, $(1, "+", _m))), "@", $()), _m);
			
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
						
						sequenceUnappendInLast($(";"));
						simplifyMeaningOfRepeat2InLast();
						canonicalizeLast();
						simplifySequenceAppendAndConcatenateInLast();
						
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
								
								autobindTrim("meaning_of_repeat_1", $1(app("allocate", str("i"), 1)), 0, "i", 0, $1(app("write", str("result"), app("read", str("i"), 0), 1)));
								
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
								
								autobind("meaning_of_write_1", (Object) "result", 0, 1, sequence(";", app("allocate", str("i"), 1), app("repeat", 0, str("i"), 0, block(app("write", str("result"), app("read", str("i"), 0), 1)))));
								autoapplyOnce(name(-1));
								
								simplifySequenceAppendInLast();
								
								conclude();
							}
							
							{
								subdeduction();
								
								bind("meaning_of_repeat_0",
										$1(app("allocate", str("i"), 1)),
										"i", 0, "result", 0,
										$1(app("write", str("result"), app("read", str("i"), 0), 1)));
								
								leftEliminateDisjunction(name(-1));
								
								simplifySequenceAppendInLast();
								
								{
									subdeduction();
									
									autobindTrim("meaning_of_allocate_0", $(), "i", 1, "result", 0);
									
									simplifySequenceAppendInLast();
									
									conclude();
								}
								
								rewriteRight(name(-2), name(-1));
								
								conclude();
							}
							
							rewriteRight(name(-2), name(-1));
							
							autobindTrim(resultReality, 0);
							
							autoapply(name(-2));
							
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
					
					final String definitionOfP = name(-1);
					
					{
						subdeduction();
						
						new ToJavaHelper().compute(left(proposition(definitionOfP)));
						rewrite(name(-1), definitionOfP);
						canonicalizeLast();
						
						conclude();
					}
					
					{
						subdeduction();
						
						{
							subdeduction();
							
							autodeduce($(0, LE, m));
							autodeduce($(0, "<", $(1, "+", $(m, "+", 1))));
							
							recall(name(-3));
							sequenceUnappendInLast($(";"));
							simplifyMeaningOfRepeat2InLast();
							simplifySequenceAppendAndConcatenateInLast();
							canonicalizeLast();
							
							conclude();
						}
						
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
								
								autobindTrim("meaning_of_repeat_1",
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
						
						autobind("meaning_of_write_0",
								sequence(";", vp0.get(), vp1.get()),
								va.get(),
								vi.get(),
								va.get(),
								0,
								1);
						
						simplifySequenceAppendInLast();
						
						{
							subdeduction();
							
							autodeduce($(0, LE, m));
							autodeduce($(0, "<", $(1, "+", m)));
							autobindTrim("conversion<>", left(proposition(-1)), right(proposition(-1)));
							rewrite(name(-2), name(-1));
							autobindTrim(">_implies_not_equal", left(proposition(-1)), right(proposition(-1)));
							
							conclude();
						}
						
						rightEliminateDisjunction(name(-2));
						
						commuteEquality(name(-1));
						
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
								
								autobindTrim("definition_of_range", $(1, "+", $(m, "+", 1)), k);
								
								{
									subdeduction();
									
									autobindTrim("definition_of_range", $(1, "+", m), k);
									rewrite(h, name(-1));
									breakConjunction(name(-1));
									
									{
										subdeduction();
										
										autobindTrim("combination_of_<<", left(proposition(-1)), right(proposition(-1)), 0, 1);
										canonicalize(left(proposition(-1)));
										rewrite(name(-2), name(-1));
										
										{
											final Variable va = new Variable("a");
											final Variable vb = new Variable("b");
											final Variable vc = new Variable("c");
											
											matchOrFail($($(va, "+", vb), "+", vc), right(proposition(-1)));
											
											autobindTrim("associativity_of_+_+_in_" + R, va.get(), vb.get(), vc.get());
											rewrite(name(-2), name(-1));
										}
										
										conclude();
									}
									
									autobindTrim("introduction_of_conjunction", proposition(-3), proposition(-1));
									
									conclude();
								}
								
								rewriteRight(name(-1), name(-2));
								
								conclude();
							}
							
							autoapply(name(-2));
							
							conclude();
						}
						
						autoapply("induction_simplified_condition_n.2");
						
						new ToJavaHelper().compute(left(condition(scope(proposition(-1)))));
						autobindTrim(name(-2), right(proposition(-1)));
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
				
				autobindTrim("definition_of_positives", _n);
				rewrite(last(deduction().getParent().getConditionNames()), name(-1));
				
				conclude();
			}
			
			breakConjunction(name(-1));
			
			autodeduce($(_n, IN, Z));
			
			{
				subdeduction();
				
				autobindTrim("equality_<" + LE, 0, _n);
				
				rewrite(name(-3), name(-1));
				canonicalizeLast();
				
				conclude();
			}
			
			autodeduce($(_n, IN, R));
			
			{
				subdeduction();
				
				autoapply("full_induction");
				
				canonicalizeForallIn(proposition(-1));
				rewrite(name(-2), name(-1));
				
				bind(name(-1), $(_n, "-", 1));
				autoapply(name(-1));
				
				subsituteLast();
				canonicalizeLast();
				
				conclude();
			}
			
			concludeGoal();
		}
		
		if (false) {
			abort();
		}
	}
	
	public static final void simplifyMeaningOfRepeat2InLast() {
		new Simplifier(Simplifier.Mode.DEFINE)
		.add(newMeaningOfRepeat2SimplificationRule())
		.apply(right(proposition(-1)));
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
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vz = new Variable("z");
		
		matchOrFail($rule($(vx, LOR, vy), vz), proposition(targetName));
		
		autobindTrim("left_elimination_of_disjunction", vx.get(), vy.get(), vz.get());
	}
	
	public static final void rightEliminateDisjunction(final String targetName) {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vz = new Variable("z");
		
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
		final Variable vX = new Variable("X");
		final Variable ve = new Variable("e");
		
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
			}
			
			autobindTrim("commutativity_of_equality",
					left(proposition(-1)), right(proposition(-1)));
			
			conclude();
			
			return true;
		});
	}
	
	public static final TryRule<Object> newMeaningOfRepeat2SimplificationRule() {
//		{
//			final Object _a = $new("a");
//			final Object _i = $new("i");
//			final Object _n = $new("n");
//			final Object _p = $new("p");
//			final Object _q = $new("q");
//			
//			final Object instruction = instructions(_p, app("repeat", _n, str(_a), _i, $("()->{", _q, "}")));
//			final Object instruction2 = $("sequence_concatenate", ";",
//					_p,
//					$("sequence_concatenate", ";",
//							$1(app("repeat", $(_n, "-", 1), str(_a), _i, $("()->{", _q, "}"))),
//							_q));
//			
//			suppose("meaning_of_repeat_2",
//					$forall(_p, _a, _i, _n, _q,
//							$rule($($(_n, IN, POS)), $(instruction, "=", instruction2))));
//		}
		
		final Variable va = new Variable("a");
		final Variable vi = new Variable("i");
		final Variable vn = new Variable("n");
		final Variable vp = new Variable("p");
		final Variable vq = new Variable("q");
		
		return tryMatch(instructions(vp, app("repeat", vn, str(va), vi, $("()->{", vq, "}"))), (e, m) -> {
			autobindTrim("meaning_of_repeat_2", vp.get(), va.get(), vi.get(), vn.get(), vq.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSequenceAppendSimplificationRule() {
		final Variable vs = new Variable("s");
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		
		return tryMatch($("sequence_append", vs, vx, vy), (e, m) -> {
			computeSequenceAppend(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSequenceConcatenateSimplificationRule() {
		final Variable vs = new Variable("s");
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		
		return tryMatch($("sequence_concatenate", vs, vx, vy), (e, m) -> {
			computeSequenceConcatenate(vs.get(), vx.get(), vy.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newSubstitutionSimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable ve = new Variable("e");
		final Variable vi = new Variable("i");
		
		return tryMatch($(vx, "|", ve, "@", vi), (e, m) -> {
			substitute(vx.get(), toMap(ve.get()), toInts(vi.get()));
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallInSimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		return tryMatch($(FORALL, vx, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in", vx.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallIn2SimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		return tryMatch($(FORALL, vx, ",", vy, IN, vX, vP), (e, m) -> {
			bind("definition_of_forall_in_2", vx.get(), vy.get(), vX.get(), vP.get());
			
			return true;
		});
	}
	
	public static final TryRule<Object> newForallIn3SimplificationRule() {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vz = new Variable("z");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
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
	
	public static final void supposeDefinitionsForCLCode() {
		{
			final Object _X = $new("X");
			final Object _i = $new("i");
			final Object _j = $new("j");
			final Object _n = $new("n");
			
			suppose("definition_of_vector_generator_to_CL",
					$forall(_X, _i,
							$(FORALL, _n, IN, N,
									$rule($(FORALL, _j, IN, $(N, "_", $("<", _n)), $($(_X, "|", $1($replacement(_i, _j)), "@", $()), IN, R)),
											$($("to_CL", $(p(_X), "_", $(_i, "<", _n))), "=", sequence(";\n",
													"	int const gid = get_global_id(0)",
													$("	result[gid] = ", $($("to_CL", _X), "|", $1($replacement(_i, "gid")), "@", $())),
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
					
					autobind("definition_of_vector_generator_to_CL", _X, _i, _n);
					autoapplyOnce(name(-1));
					
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
								autobind("definition_of_forall_in", j, $(N, "_", $("<", _n)), $($(_X, "|", $1($replacement(_i, j)), "@", $()), IN, R));
								
								rewriteRight(name(-2), name(-1));
							}
							
							conclude();
						}
						
						autoapplyOnce(name(-2));
						
						this.compute($("to_CL", _X));
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
					autobindTrim("definition_of_real_to_CL", m.get(vX));
					
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
						
						autobind("definition_of_vector_generator_to_java", _X, _i, _n);
						autoapplyOnce(name(-1));
						
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
								autobind("definition_of_forall_in", j, $(N, "_", $("<", _n)), $($(_X, "|", $1($replacement(_i, j)), "@", $()), IN, R));
								
								rewriteRight(name(-2), name(-1));
							}
							
							conclude();
						}
						
						autoapplyOnce(name(-2));
						
						{
							this.compute($("to_java", _n));
							
							rewrite(name(-2), name(-1));
						}
						
						{
							this.compute($("to_java", _X));
							
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
					autobindTrim("definition_of_real_to_java", m.get(vX));
					
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
