package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Propositions.breakConjunction;
import static autodiff.reasoning.deductions.Propositions.deduceConjunctionLeft;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalize;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalizeIn;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalizeLast;
import static autodiff.reasoning.deductions.ScalarAlgebra.newElementarySimplificationRule;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.tactics.Stack.PropositionDescription.potentialJustificationsFor;
import static multij.rules.Variable.matchOrFail;
import static multij.tools.Tools.*;

import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.Auto.Simplifier;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;
import autodiff.reasoning.tactics.PatternMatching;
import autodiff.reasoning.tactics.Stack.PropositionDescription;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.rules.Rules;
import multij.rules.TryRule;
import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;

/**
 * @author codistmonk (creation 2016-09-09)
 */
public final class Autodiff {
	
	private Autodiff() {
		throw new IllegalInstantiationException();
	}
	
	public static final Object PI = $("Π");
	
	public static final Object SUM = $("∑");
	
	public static final Deduction AUTODIFF = Basics.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			ScalarFunctions.load();
			
			supposeEliminationOfParentheses();
			
			supposeTypeOfPowersetOfReals();
			
			deducePositivesSubsetNaturals();
			deducePositivesInUhm();
			supposeDefinitionOfMs();
			supposeTypeOfFlat();
			supposeDefinitionOfSingleton();
			
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
				final Object _n = $new("n");
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _X = $new("X");
				final Object _i = $new("i");
				
				suppose("definition_of_dot_product",
						$forall(_X,
								$(FORALL, _n, IN, POS,
										$(FORALL, _x, ",", _y, IN, $(_X, "^", _n),
												$($(_x, "⋅", _y), "=", $(SUM, "_", $(_i, "<", _n), $($(_x, "_", _i), "*", $(_y, "_", _i))))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _i = $new("i");
				final Object _j = $new("j");
				
				final Object _n1 = $(_n, "-", 1);
				
				suppose("definition_of_multidimensional_strides",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n),
										$($("strides", _s), "=", $(p($(PI, "_", $(_j, "<", $(_n1, "-", _i)), $(_s, "_", $(_n1, "-", _j)))), "_", $(_i, "<", _n))))));
			}
			
			{
				final Object _s = $new("s");
				final Object _y = $new("y");
				
				suppose("definition_of_sequence_prepend_0",
						$forall(_s, _y,
								$($("sequence_prepend", _s, _y, $()), "=", $1(_y))));
			}
			
			{
				final Object _s = $new("s");
				final Object _x0 = $new("x0");
				final Object _y = $new("y");
				
				suppose("definition_of_sequence_prepend_1",
						$forall(_s, _x0, _y,
								$($("sequence_prepend", _s, _y, $1(_x0)), "=", $(_y, $(_s, _x0)))));
			}
			
			{
				final Object _s = $new("s");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				final Object _y = $new("y");
				
				suppose("definition_of_sequence_prepend_2",
						$forall(_s, _x0, _x1, _y,
								$($("sequence_prepend", _s, _y, $(_x0, _x1)), "=", $(_y, $(_s, _x0, _x1)))));
			}
			
			{
				final Object _s = $new("s");
				final Object _x0 = $new("x0");
				
				suppose("definition_of_sequence_prefix_0",
						$forall(_s, _x0,
								$($("sequence_prefix", _s, $1(_x0)), "=", $())));
			}
			
			{
				final Object _s = $new("s");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				
				suppose("definition_of_sequence_prefix_1",
						$forall(_s, _x0, _x1,
								$($("sequence_prefix", _s, $(_x0, $(_s, _x1))), "=", $1(_x0))));
			}
			
			{
				final Object _s = $new("s");
				final Object _x0 = $new("x0");
				final Object _x1 = $new("x1");
				final Object _x2 = $new("x2");
				
				suppose("definition_of_sequence_prefix_2",
						$forall(_s, _x0, _x1, _x2,
								$($("sequence_prefix", _s, $(_x0, $(_s, _x1, _x2))), "=", $("sequence_prepend", _s, _x0, $("sequence_prefix", _s, $(_x1, _x2))))));
			}
			
			{
				final Object _n = $(1);
				final Object _s = $new("s");
				final Object _j = $new("j");
				
				suppose("definition_of_indices_type_0",
						$(FORALL, _s, IN, $(POS, "^", _n),
								$forall(_j,
										$($(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j)))),
												"=", $("sequence_append", CROSS, $(), $(N, "_", $("<", $(_s, "_", 0))))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _j = $new("j");
				
				final Object _m = $(_n, "-", 1);
				
				suppose("definition_of_indices_type_1",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n),
										$forall(_j,
												$($(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j)))),
														"=", $("sequence_append", CROSS, $(CROSS, "_", $(_j, "<", _m), $(N, "_", $("<", $($("sequence_prefix", ",", _s), "_", _j)))), $(N, "_", $("<", $(_s, "_", _m)))))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _i = $new("i");
				final Object _j = $new("j");
				
				suppose("definition_of_index_from_indices",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n),
										$(FORALL, _i, IN, $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j)))),
												$($("index_from_indices", _s, _i), "=", $(_i, "⋅", $("strides", _s)))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _x = $new("x");
				final Object _i = $new("i");
				final Object _j = $new("j");
				
				suppose("definition_of_multidimensional_access",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n),
										$(FORALL, _x, IN, $("M", "_", _s),
												$(FORALL, _i, IN, $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j)))),
														$($(_x, "_", _i), "=", $($(_x, ".v"), "_", $("index_from_indices", _s, _i))))))));
			}
			
			{
				final Object _x = $new("x");
				final Object _i = $new("i");
				final Object _X = $new("X");
				final Object _n = $new("n");
				
				// TODO prove
				
				suppose("type_of_vector_access",
						$forall(_X, _n,
								$(FORALL, _x, IN, $(_X, "^", _n),
										$(FORALL, _i, IN, $(N, "_", $("<", _n)),
												$($(_x, "_", _i), IN, _X)))));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				
				suppose("definition_of_vector_generator_0",
						$forall(_X, _i,
								$($(p(_X), "_", $(_i, "<", 0)), "=", $())));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				final Object _n = $new("n");
				
				final Object _m = $(_n, "-", 1);
				
				suppose("definition_of_vector_generator_1",
						$forall(_X, _i,
								$(FORALL, _n, IN, POS,
										$($(p(_X), "_", $(_i, "<", _n)),
												"=", $("sequence_append", ",", $(p(_X), "_", $(_i, "<", _m)), $(_X, GIVEN, $1($replacement(_i, _m)), AT, $()))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				
				suppose("definition_of_sum_0",
						$forall(_X, _i,
								$($(SUM, "_", $(_i, "<", 0), _X), "=", 0)));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				final Object _n = $new("n");
				
				final Object m = $(_n, "-", 1);
				
				suppose("definition_of_sum_1",
						$forall(_X, _i,
								$(FORALL, _n, IN, POS,
										$($(SUM, "_", $(_i, "<", _n), _X), "=", $($(SUM, "_", $(_i, "<", m), _X), "+", $(_X, GIVEN, $1($replacement(_i, m)), AT, $()))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				
				suppose("definition_of_product_0",
						$forall(_X, _i,
								$($(PI, "_", $(_i, "<", 0), _X), "=", 1)));
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				final Object _n = $new("n");
				
				final Object m = $(_n, "-", 1);
				
				suppose("definition_of_product_1",
						$forall(_X, _i,
								$(FORALL, _n, IN, POS,
										$($(PI, "_", $(_i, "<", _n), _X), "=", $($(PI, "_", $(_i, "<", m), _X), "*", $(_X, GIVEN, $1($replacement(_i, m)), AT, $()))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _i = $new("i");
				
				suppose("type_of_multidimensional_data",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n),
										$(FORALL, _X, IN, $("M", "_", _s),
												$forall(_i,
														$($(_X, ".v"), IN, $(R, "^", $(PI, "_", $(_i, "<", _n), $(_s, "_", _i)))))))));
			}
			
			for (final Object type : array(N, Z, Q, R)) {
				subdeduction("stability_of_sum_in_" + type);
				
				final Object _X = forall("X");
				final Object _i = forall("i");
				final Object _l = forall("l");
				
				suppose($(_l, IN, POS));
				
				{
					final Object _j = $new("j");
					
					suppose("stability_of_X",
							$(FORALL, _j, IN, $(N, "_", $("<", _l)), $($(_X, GIVEN, $1($replacement(_i, _j)), AT, $()), IN, type)));
				}
				
				final Object _n = $new("n");
				final Object sum = $(SUM, "_", $(_i, "<", _n), _X);
				final Object _Pn = $rule($(_n, "<", $(_l, "+", 1)), $(sum, IN, type));
				
				bind("induction_principle", _Pn, _n);
				
				{
					subdeduction("induction_0");
					
					substitute(_Pn, map(_n, 0));
					
					{
						subdeduction();
						
						suppose($(0, "<", $(_l, "+", 1)));
						
						bind("definition_of_sum_0", _X, _i);
						autodeduce($(right(proposition(-1)), IN, type));
						rewriteRight(name(-1), name(-2));
						
						conclude();
					}
					
					rewriteRight(name(-1), name(-2));
					
					conclude();
				}
				
				apply(name(-2), name(-1));
				
				{
					subdeduction("induction_n");
					
					{
						subdeduction();
						
						final Object _m = forall("m");
						
						suppose($(_m, IN, N));
						
						{
							subdeduction();
							
							final Object _Pm = $rule($(_m, "<", $(_l, "+", 1)), $($(SUM, "_", $(_i, "<", _m), _X), IN, type));
							
							suppose("induction_n_condition", _Pm);
							
							final Object _m1 = $(_m, "+", 1);
							
							{
								subdeduction();
								
								substitute(_Pm, map(_m, _m1));
								
								{
									subdeduction();
									
									autodeduce($(_m1, IN, POS));
									
									autobindTrim("definition_of_sum_1", _X, _i, _m1);
									
									canonicalize(right(proposition(-1)));
									
									rewrite(name(-2), name(-1));
									
									conclude();
								}
								
								rewrite(name(-2), name(-1));
								
								conclude();
							}
							
							{
								subdeduction();
								
								final Object inductionNSimplification = proposition(-1);
								
								suppose($(_m1, "<", $(_l, "+", 1)));
								
								{
									subdeduction();
									
									autobindTrim("preservation_of_<_under_addition", left(proposition(-1)), right(proposition(-1)), -1);
									canonicalizeLast();
									
									conclude();
								}
								
								autobindTrim("stability_of_X", _m);
								
								{
									subdeduction();
									
									autodeduce($(_m, "<", _m1));
									autobindTrim("transitivity_of_<", _m, _m1, $(_l, "+", 1));
									
									conclude();
								}
								
								autoapply("induction_n_condition");
								
								{
									final Variable vx = v("x");
									final Variable vy = v("y");
									
									matchOrFail($(v("?"), "=", $rule(v("?"), $($(vx, "+", vy), IN, type))), inductionNSimplification);
									
									autobindTrim("stability_of_+_in_" + type, vx.get(), vy.get());
								}
								
								conclude();
							}
							
							rewriteRight(name(-1), name(-2));
							
							conclude();
						}
						
						conclude();
					}
					
					compactForallIn(name(-1));
					
					conclude();
				}
				
				{
					subdeduction();
					
					autodeduce($(proposition(-1), "=", condition(proposition(-2))));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				apply("conclusion", name(-3), name(-1));
				
				conclude();
			}
			
			{
				final Object _X = $new("X");
				final Object _i = $new("i");
				final Object _Y = $new("Y");
				final Object _j = $new("j");
				final Object _n = $new("n");
				
				suppose("equality_of_" + CROSS + "_sequence",
						$forall(_X, _i, _Y, _j,
								$(FORALL, _n, IN, N,
										$rule($($(_X, GIVEN, $1($replacement(_i, _j)), AT, $()), "=", _Y), $($(_Y, GIVEN, $1($replacement(_j, _i)), AT, $()), "=", _X),
												$($(CROSS, "_", $(_i, "<", _n), _X), "=", $(CROSS, "_", $(_j, "<", _n), _Y))))));
			}
			
			{
				final Variable vX = v("X");
				final Variable vi = v("i");
				final Variable vY = v("Y");
				final Variable vj = v("j");
				final Variable vn = v("n");
				
				Auto.hintAutodeduce(tryMatch($($(CROSS, "_", $(vi, "<", vn), vX), "=", $(CROSS, "_", $(vj, "<", vn), vY)), (e, m) -> {
					final Object _X = vX.get();
					final Object _i = vi.get();
					final Object _Y = vY.get();
					final Object _j = vj.get();
					final Object _n = vn.get();
					
					subdeduction();
					
					substitute(_X, map(_i, _j));
					substitute(_Y, map(_j, _i));
					autobindTrim("equality_of_" + CROSS + "_sequence", _X, _i, _Y, _j, _n);
					
					conclude();
					
					return true;
				}));
			}
			
			{
				final Variable vX = v("X");
				final Variable vi = v("i");
				final Variable vn = v("n");
				final Variable vT = v("T");
				
				Auto.hintAutodeduce(tryMatch($($(SUM, "_", $(vi, "<", vn), vX), IN, vT), (e, m) -> {
					final Object _X = vX.get();
					final Object _i = vi.get();
					final Object _n = vn.get();
					final Object _T = vT.get();
					
					subdeduction();
					
					autobind("stability_of_sum_in_" + _T, _X, _i, _n);
					autoapplyOnce(name(-1));
					
					{
						subdeduction();
						
						{
							final Variable vJ = v("J");
							
							matchOrFail($(FORALL, v("?"), IN, vJ, v("?")), condition(proposition(-1)));
							
							subdeduction();
							
							final Object _j = forall("j");
							
							suppose($(_j, IN, vJ.get()));
							
							substitute(_X, map(_i, _j));
							canonicalize(right(proposition(-1)));
							rewrite(name(-2), name(-1));
							
							autodeduce($(right(proposition(-1)), IN, _T));
							rewriteRight(name(-1), name(-2));
							
							conclude();
						}
						
						ScalarAlgebra.buildForallIn();
						
						autodeduce($(proposition(-1), "=", condition(proposition(-3))));
						
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					autobindTrim(name(-2), _n);
					
					conclude();
					
					return true;
				}));
			}
			
			{
				final Variable vx = v("x");
				final Variable vi = v("i");
				final Variable vj = v("j");
				final Variable vX = v("X");
				
				Auto.hintAutodeduce(tryMatch($($(vx, "_", tuple(vi, vj)), IN, vX), (e, m) -> {
					final Object _x = vx.get();
					final Object _i = vi.get();
					final Object _j = vj.get();
					final Object _X = vX.get();
					
					final Variable vs = v("s");
					
					for (final Pair<PropositionDescription, PatternMatching> pair : potentialJustificationsFor($(_x, IN, $("M", "_", vs)))) {
						pair.getSecond().getMapping().forEach(Variable::set);
						
						final Object _s = vs.get();
						
						if (trySubdeduction(() -> {
							{
								subdeduction();
								
								autobindTrim("definition_of_indices_type_1", $(sequenceLength(",", _s)), _s, $new("k"));
								canonicalizeLast();
								simplifySequencePrefixInLast();
								
								simplifyDefinitionOfIndicesInLast();
								
								simplifySequenceAppendInLast();
								simplifyVectorAccessInLast();
								simplifySequenceTailInLast();
								simplifyVectorAccessInLast();
								simplifySequenceTailInLast();
								simplifySequenceHeadInLast();
								
								conclude();
							}
							
							{
								final Variable vX_ = v("X");
								final Variable vY_ = v("Y");
								
								matchOrFail($(v("?"), "=", sequence(CROSS, vX_, vY_)), proposition(-1));
								
								subdeduction();
								
								beginCartesianProduct(_i, vX_.get());
								appendToCartesianProduct(_j, vY_.get());
								
								conclude();
							}
							
							rewriteRight(name(-1), name(-2));
							
							{
								subdeduction();
								
								autobind("definition_of_multidimensional_access", $(2), _s, _x, tuple(_i, _j));
								autodeduce($(right(proposition(-2)), "=", right(condition(proposition(-1)))));
								rewrite(name(-3), name(-1));
								autoapply(name(-3));
								
								conclude();
							}
							
							{
								subdeduction();
								
								autobind("definition_of_index_from_indices", $(2), _s, tuple(_i, _j));
								autodeduce($(right(proposition(-3)), "=", right(condition(proposition(-1)))));
								rewrite(name(-4), name(-1));
								autoapply(name(-3));
								
								conclude();
							}
							
							rewrite(name(-2), name(-1));
							
							{
								subdeduction();
								
								autobindTrim("definition_of_multidimensional_strides", $(2), _s);
								
								simplifyVectorGeneratorInLast();
								simplifySequenceAppendInLast();
								simplifySubstitutionsAndElementaryInLast();
								simplifyProductInLast();
								simplifySubstitutionsAndElementaryInLast();
								simplifyVectorAccessInLast();
								simplifySequenceTailInLast();
								simplifyVectorAccessInLast();
								simplifySequenceHeadInLast();
								
								canonicalizeLast();
								
								conclude();
							}
							
							rewrite(name(-2), name(-1));
							
							{
								final Variable vx_ = v("x");
								final Variable vy_ = v("y");
								
								matchOrFail($(v(), "=", $(v(), "_", $(vx_, "⋅", vy_))), proposition(-1));
								
								subdeduction();
								
								autobindTrim("definition_of_dot_product", N, $(2), vx_.get(), vy_.get());
								
								simplifySumInLast();
								simplifySubstitutionsAndElementaryInLast();
								simplifyVectorAccessInLast();
								simplifySequenceTailInLast();
								simplifyVectorAccessInLast();
								simplifySequenceHeadInLast();
								canonicalizeLast();
								
								conclude();
							}
							
							rewrite(name(-2), name(-1));
							
							{
								subdeduction();
								
								{
									subdeduction();
									
									final Variable vx_ = v("x");
									final Variable vi_ = v("i");
									
									matchOrFail($(v(), "=", $(vx_, "_", vi_)), proposition(-1));
									
									final Object _k = $new("k");
									
									autobindTrim("type_of_multidimensional_data", $(2), _s, _x, _k);
									
									final Variable vX_ = v("X");
									final Variable vn_ = v("n");
									
									matchOrFail($(v(), IN, $(vX_, "^", vn_)), proposition(-1));
									
									autobind("type_of_vector_access", vX_.get(), vn_.get(), vx_.get(), vi_.get());
									
									{
										subdeduction();
										
										bind("identity", proposition(-1));
										simplifyProductInLast();
										simplifySubstitutionsAndElementaryInLast();
										simplifyVectorAccessInLast();
										simplifySequenceTailInLast();
										simplifyVectorAccessInLast();
										simplifySequenceHeadInLast();
										
										canonicalize(right(proposition(-1)));
										rewrite(name(-2), name(-1));
										
										conclude();
									}
									
									rewrite(name(-2), name(-1));
									
									conclude();
								}
								
								autoapply(name(-1));
								
								conclude();
							}
							
							rewriteRight(name(-1), name(-2));
						})) {
							return true;
						}
					}
					
					return false;
				}));
			}
			
			{
				final Variable vx = v("x");
				final Variable vi = v("i");
				final Variable vX = v("X");
				
				Auto.hintAutodeduce(tryMatch($($(vx, "_", vi), IN, vX), (e, m) -> {
					final Object _x = vx.get();
					final Object _i = vi.get();
					final Object _X = vX.get();
					
					final Variable vY = v("Y");
					final Variable vn = v("n");
					
					for (final Pair<PropositionDescription, PatternMatching> pair : potentialJustificationsFor($(_x, IN, $(vY, "^", vn)))) {
						pair.getSecond().getMapping().forEach(Variable::set);
						
						final Object _Y = vY.get();
						final Object _n = vn.get();
						
						if (trySubdeduction(() -> {
							{
								subdeduction();
								
								autobindTrim("definition_of_subset", _X, _Y);
								autodeduce(left(proposition(-1)));
								rewrite(name(-1), name(-2));
								
								conclude();
							}
							
							{
								subdeduction();
								
								canonicalizeIn(pair.getFirst().getName());
								
								autobind("type_of_vector_access", _Y, _n, _x, _i);
								canonicalizeLast();
								autoapply(name(-1));
								
								conclude();
							}
							
							bind(name(-2), left(proposition(-1)));
							apply(name(-1), name(-2));
						})) {
							return true;
						}
					}
					
					return false;
				}));
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
	
	public static final Object cartesian(final Object _s, final Object _j, final Object _n) {
		return $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j))));
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
	
	public static final int[] toInts(final List<Object> numbers) {
		return numbers.stream().mapToInt(n -> ((Number) n).intValue()).toArray();
	}
	
	public static final Object floor(final Object expression) {
//		return $("⎣", expression, "⎦");
		return $("floor", expression);
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
	
	public static final void simplifySequencePrefixInLast() {
		final Simplifier s = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vsep = v("sep");
			final Variable vx0 = v("x0");
			
			s.add(tryMatch($("sequence_prefix", vsep, $1(vx0)), (_e, _m) -> {
				bind("definition_of_sequence_prefix_0", vsep.get(), vx0.get());
				
				return true;
			}));
		}
		
		{
			final Variable vsep = v("sep");
			final Variable vx0 = v("x0");
			final Variable vx1 = v("x1");
			
			s.add(tryMatch($("sequence_prefix", vsep, $(vx0, $(vsep, vx1))), (_e, _m) -> {
				bind("definition_of_sequence_prefix_1", vsep.get(), vx0.get(), vx1.get());
				
				return true;
			}));
		}
		
		s.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifyDefinitionOfIndicesInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Object _n = $(1);
			final Variable vs_ = v("s");
			final Variable vj_ = v("j");
			
			simplifier.add(tryMatch($(CROSS, "_", $(vj_, "<", _n), $(N, "_", $("<", $(vs_, "_", vj_)))), (_e, _m) -> {
				autobindTrim("definition_of_indices_type_0", vs_.get(), vj_.get());
				
				return true;
			}));
		}
		
		{
			final Variable vn = v("n");
			final Variable vs_ = v("s");
			final Variable vj_ = v("j");
			
			simplifier.add(tryMatch($(CROSS, "_", $(vj_, "<", vn), $(N, "_", $("<", $(vs_, "_", vj_)))), (_e, _m) -> {
				autobindTrim("definition_of_indices_type_1", vn.get(), vs_.get(), vj_.get());
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifyVectorAccessInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vx_ = v("x");
			
			simplifier.add(tryMatch($(vx_, "_", 0), (_e, _m) -> {
				autobindTrim("definition_of_vector_access_0", R, sequenceLength(",", vx_.get()), vx_.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx_ = v("x");
			final Variable vi_ = v("i");
			
			simplifier.add(tryMatch($(vx_, "_", vi_), (_e, _m) -> {
				subdeduction();
				
				autobindTrim("definition_of_vector_access_i", R, sequenceLength(",", vx_.get()), vi_.get(), vx_.get());
				canonicalizeLast();
				
				conclude();
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceHeadInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vx0 = v("x0");
			
			simplifier.add(tryMatch($("sequence_head", $1(vx0)), (e_, m_) -> {
				bind("definition_of_sequence_head_1", vx0.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx0 = v("x0");
			final Variable vx1 = v("x1");
			
			simplifier.add(tryMatch($("sequence_head", $(vx0, vx1)), (e_, m_) -> {
				bind("definition_of_sequence_head_2", vx0.get(), vx1.get());
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySequenceTailInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vs_ = v("s");
			final Variable vx0 = v("x0");
			final Variable vx1 = v("x1");
			
			simplifier.add(tryMatch($("sequence_tail", vs_, $(vx0, $(vs_, vx1))), (e_, m_) -> {
				bind("definition_of_sequence_tail_1", vs_.get(), vx0.get(), vx1.get());
				
				return true;
			}));
		}
		
		{
			final Variable vs_ = v("s");
			final Variable vx0 = v("x0");
			final Variable vx1 = v("x1");
			final Variable vx2 = v("x2");
			
			simplifier.add(tryMatch($("sequence_tail", vs_, $(vx0, $(vs_, vx1, vx2))), (e_, m_) -> {
				bind("definition_of_sequence_tail_2", vs_.get(), vx0.get(), vx1.get(), vx2.get());
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifyVectorGeneratorInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			
			simplifier.add(tryMatch($($(p(vX_), "_", $(vi_, "<", 0))), (e_, m_) -> {
				bind("definition_of_vector_generator_0", vX_.get(), vi_.get());
				
				return true;
			}));
		}
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			final Variable vn_ = v("n");
			
			simplifier.add(tryMatch($($(p(vX_), "_", $(vi_, "<", vn_))), (e_, m_) -> {
				subdeduction();
				
				autobindTrim("definition_of_vector_generator_1", vX_.get(), vi_.get(), vn_.get());
				canonicalize(right(proposition(-1)));
				rewrite(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifyProductInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			
			simplifier.add(tryMatch($($(PI, "_", $(vi_, "<", 0), vX_)), (e_, m_) -> {
				bind("definition_of_product_0", vX_.get(), vi_.get());
				
				return true;
			}));
		}
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			final Variable vn_ = v("n");
			
			simplifier.add(tryMatch($($(PI, "_", $(vi_, "<", vn_), vX_)), (e_, m_) -> {
				subdeduction();
				
				autobindTrim("definition_of_product_1", vX_.get(), vi_.get(), vn_.get());
				canonicalize(right(proposition(-1)));
				rewrite(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
	public static final void simplifySumInLast() {
		final Simplifier simplifier = new Simplifier(Mode.DEFINE);
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			
			simplifier.add(tryMatch($($(SUM, "_", $(vi_, "<", 0), vX_)), (e_, m_) -> {
				bind("definition_of_sum_0", vX_.get(), vi_.get());
				
				return true;
			}));
		}
		
		{
			final Variable vX_ = v("X");
			final Variable vi_ = v("i");
			final Variable vn_ = v("n");
			
			simplifier.add(tryMatch($($(SUM, "_", $(vi_, "<", vn_), vX_)), (e_, m_) -> {
				subdeduction();
				
				autobindTrim("definition_of_sum_1", vX_.get(), vi_.get(), vn_.get());
				canonicalize(right(proposition(-1)));
				rewrite(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		simplifier.simplifyCompletely(proposition(-1));
	}
	
}
