package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Autodiff.*;
import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Basics.rewriteRight;
import static autodiff.reasoning.deductions.Propositions.breakConjunction;
import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalize;
import static autodiff.reasoning.deductions.Sequences.computeSequenceAppend;
import static autodiff.reasoning.deductions.Sequences.flattenSequence;
import static autodiff.reasoning.deductions.Sequences.sequence;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.N;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.PatternMatching.matchOrFail;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.tactics.Auto.Simplifier;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;

import java.util.List;

import multij.rules.TryRule;
import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-09-09)
 */
public final class ToJavaCode {
	
	private ToJavaCode() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(ToJavaCode.class, "loaded")) {
			return;
		}
		
		supposeDefinitionsForJavaCode();
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
															block(app("write", str("result"), app("read", str("i"), 0) , $($("to_java", _X), GIVEN, $1($replacement($("to_java", _i), app("read", str("i"), 0))), AT, $()))))))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_real_to_java",
					$(FORALL, _x, IN, R,
							$($("to_java", _x), "=", _x)));
		}
		
		{
			final Object _X = $new("X");
			
			suppose("definition_of_floor_to_java",
					$forall(_X,
							$($("to_java", floor(_X)), "=", app("floor", $("to_java", _X)))));
		}
		
		for (final Object op : array("+", "-", "*", "/")) {
			final Object _X = $new("X");
			final Object _Y = $new("Y");
			
			suppose("definition_of_" + op + "_to_java",
					$forall(_X, _Y,
							$($("to_java", $(_X, op, _Y)), "=", $($("to_java", _X), op, $("to_java", _Y)))));
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
		
		if (true) {
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
						
//						new ToJavaHelper().compute(left(proposition(-1)));
						{
							subdeduction();
							
							bind("identity", left(proposition(-1)));
							computeToJava(proposition(-1));
							
							conclude();
						}
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
						{
							subdeduction();
							
							{
								subdeduction();
								
								sequenceUnappendInLast($(";"));
								
								{
									final Variable vp = v("p");
									final Variable vy = v("y");
									
									matchOrFail($("sequence_append", ";", vp, vy), right(proposition(-1)));
									
									final Variable vf = v("f");
									final Variable vx = v("x");
									
									matchOrFail(appx(vf, vx), vy.get());
									
									bind("meaning_of_read_in_arguments", vp.get(), vf.get(), vx.get(), "i", 0);
								}
								
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
						
//						new ToJavaHelper().compute(left(proposition(definitionOfP)));
						{
							subdeduction();
							
							bind("identity", left(proposition(definitionOfP)));
							computeToJava(proposition(-1));
							
							conclude();
						}
						rewrite(name(-1), definitionOfP);
						canonicalizeLast();
						
						conclude();
					}
					
					{
						subdeduction();
						
						{
							subdeduction();
							
							sequenceUnappendInLast($(";"));
							simplifyMeaningOfRepeat2InLast();
							simplifySequenceAppendAndConcatenateInLast();
							canonicalizeLast();
							
							conclude();
						}
						
						{
							subdeduction();
							
							final Variable vp0 = v("p0");
							final Variable vp1 = v("p1");
							final Variable vf = v("f");
							final Variable vx = v("x");
							
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
						
						final Variable vp0 = v("p0");
						final Variable vp1 = v("p1");
						final Variable va = v("a");
						final Variable vi = v("i");
						
						matchOrFail($(sequence(";", vp0, vp1, app("write", str(va), vi, 1))), right(proposition(-2)));
						
						autobind("meaning_of_write_0",
								sequence(";", vp0.get(), vp1.get()),
								va.get(),
								vi.get(),
								va.get(),
								0,
								1);
						
						simplifySequenceAppendInLast();
						
						autobindTrim(">_implies_not_equal", $(1, "+", m), 0);
						
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
											final Variable va = v("a");
											final Variable vb = v("b");
											final Variable vc = v("c");
											
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
						
//						new ToJavaHelper().compute(left(condition(scope(proposition(-1)))));
						{
							subdeduction();
							
							bind("identity", left(condition(scope(proposition(-1)))));
							computeToJava(proposition(-1));
							
							conclude();
						}
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
			
			{
				subdeduction();
				
				autobindTrim("equality_<" + LE, 0, _n);
				
				rewrite(name(-2), name(-1));
				canonicalizeLast();
				
				conclude();
			}
			
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
	
	public static final TryRule<Object> newMeaningOfRepeat2SimplificationRule() {
		final Variable va = v("a");
		final Variable vi = v("i");
		final Variable vn = v("n");
		final Variable vp = v("p");
		final Variable vq = v("q");
		
		return tryMatch(instructions(vp, app("repeat", vn, str(va), vi, $("()->{", vq, "}"))), (e, m) -> {
			autobindTrim("meaning_of_repeat_2", vp.get(), va.get(), vi.get(), vn.get(), vq.get());
			
			return true;
		});
	}
	
	public static final Object instructions(final Object instructionsBefore, final Object... newInstructions) {
		Object result = instructionsBefore;
		
		for (final Object instruction : newInstructions) {
			result = $("sequence_append", ";", result, instruction);
		}
		
		return result;
	}
	
	public static final Object block(final Object... arguments) {
		return blockx(sequence(";", arguments));
	}
	
	public static final Object blockx(final Object x) {
		return $("()->{", x, "}");
	}
	
	public static final Object app(final Object name, final Object... arguments) {
		return appx(name, sequence(",", arguments));
	}
	
	public static final Object appx(final Object name, final Object x) {
		return $(name, "(", x, ")");
	}
	
	public static final Object str(final Object object) {
		return $("\"", object, "\"");
	}
	
	public static final void computeToJava(final Object expression) {
		new Simplifier(Mode.DEFINE)
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			final Variable vi = v("i");
			final Variable vn = v("n");
			
			matchOrFail($("to_java", $(p(vX), "_", $(vi, "<", vn))), e);
			
			final Object _X = vX.get();
			final Object _i = vi.get();
			final Object _n = vn.get();
			
			{
				subdeduction();
				
				autobind("definition_of_vector_generator_to_java", _X, _i, _n);
				autoapplyOnce(name(-1));
				
				{
					subdeduction();
					
					final Variable vj = v("j");
					final Variable vJ = v("J");
					final Variable vS = v("S");
					
					matchOrFail($(FORALL, vj, IN, vJ, vS), condition(proposition(-1)));
					
					final Object _S = vS.get();
					
					matchOrFail($($(_X, GIVEN, $1($replacement(_i, vj.get())), AT, $()), IN, R), _S);
					
					final Object _J = vJ.get();
					
					matchOrFail($(N, "_", $("<", _n)), _J);
					
					{
						subdeduction();
						
						final Object _j = forall("j");
						
						suppose($(_j, IN, _J));
						substitute(_X, map(_i, _j));
						autodeduce($(right(proposition(-1)), IN, R));
						rewriteRight(name(-1), name(-2));
						conclude();
					}
					
					bind("definition_of_forall_in", vj.get(), _J, _S);
					rewriteRight(name(-2), name(-1));
					
					conclude();
				}
				
				autoapply(name(-2));
				
				{
					subdeduction();
					
					bind("identity", $("to_java", _X));
					computeToJava(proposition(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				simplifySubstitutionsAndElementaryInLast();
				
				conclude();
			}
		}))
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			
			matchOrFail($("to_java", floor(vX)), e);
			
			autobindTrim("definition_of_floor_to_java", vX.get());
		}))
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			final Variable vY = v("Y");
			
			for (final String op : array("+", "-", "*", "/")) {
				if (match($("to_java", $(vX, op, vY)), e)) {
					autobindTrim("definition_of_" + op + "_to_java", vX.get(), vY.get());
					
					return;
				}
			}
			
			fail();
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			
			matchOrFail($("to_java", vx), e);
			
			autobindTrim("definition_of_real_to_java", vx.get());
		}))
		.simplifyCompletely(expression);
	}
	
}
