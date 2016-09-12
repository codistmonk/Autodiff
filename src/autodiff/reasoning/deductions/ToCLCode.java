package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Autodiff.floor;
import static autodiff.reasoning.deductions.Autodiff.simplifySubstitutionsAndElementaryInLast;
import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Basics.rewriteRight;
import static autodiff.reasoning.deductions.Sequences.sequence;
import static autodiff.reasoning.deductions.Sets.p;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.N;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.PatternMatching.matchOrFail;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.array;

import autodiff.reasoning.tactics.Auto.Simplifier;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;

import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-09-09)
 */
public final class ToCLCode {
	
	private ToCLCode() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(ToCLCode.class, "loaded")) {
			return;
		}
		
		ScalarFunctions.load();
		
		supposeDefinitionsForCLCode();
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
													$("	result[gid] = ", $($("to_CL", _X), "|", $1($replacement($("to_CL", _i), "gid")), "@", $())),
													""))))));
		}
		
		{
			final Object _X = $new("X");
			
			suppose("definition_of_floor_to_CL",
					$forall(_X,
							$($("to_CL", $("floor", _X)), "=", $("(int)", "(", $("to_CL", _X), ")"))));
		}
		
		for (final Object op : array("+", "-", "*", "/", "%", "<", ">")) {
			final Object _X = $new("X");
			final Object _Y = $new("Y");
			
			suppose("definition_of_" + op + "_to_CL",
					$forall(_X, _Y,
							$($("to_CL", $(_X, op, _Y)), "=", $($("to_CL", _X), op, $("to_CL", _Y)))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_()_to_CL",
					$forall(_x,
							$($("to_CL", p(_x)), "=", p("to_CL", _x))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_cases_otherwise_to_CL",
					$forall(_x,
							$($("to_CL", $("cases", $("", $(_x, "otherwise")))), "=", $("to_CL", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _c = $new("c");
			
			suppose("definition_of_cases_if_otherwise_to_CL",
					$forall(_x, _c, _y,
							$($("to_CL", $("cases", $("", $(_x, "if", _c), $("", $(_y, "otherwise"))))), "=", $(p("to_CL", _c), "?", p("to_CL", _x), ":", p("to_CL", _y)))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _z = $new("z");
			final Object _c = $new("c");
			final Object _d = $new("d");
			
			suppose("definition_of_cases_if_if_to_CL",
					$forall(_x, _c, _y, _d, _z,
							$($("to_CL", $("cases", $("", $(_x, "if", _c), $("", $(_y, "if", _d), _z)))), "=", $(p("to_CL", _c), "?", p("to_CL", _x), ":", p("to_CL", $("cases", $("", $(_y, "if", _d), _z)))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_real_to_CL",
					$(FORALL, _x, IN, R,
							$($("to_CL", _x), "=", _x)));
		}
	}
	
	public static final void computeToCL(final Object expression) {
		new Simplifier(Mode.DEFINE)
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			final Variable vi = v("i");
			final Variable vn = v("n");
			
			matchOrFail($("to_CL", $(p(vX), "_", $(vi, "<", vn))), e);
			
			final Object _X = vX.get();
			final Object _i = vi.get();
			final Object _n = vn.get();
			
			{
				subdeduction();
				
				autobind("definition_of_vector_generator_to_CL", _X, _i, _n);
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
					
					bind("identity", $("to_CL", _X));
					computeToCL(proposition(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				simplifySubstitutionsAndElementaryInLast();
				
				conclude();
			}
		}))
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			
			matchOrFail($("to_CL", floor(vX)), e);
			
			autobindTrim("definition_of_floor_to_CL", vX.get());
		}))
		.add(tryRule((e, m) -> {
			final Variable vX = v("X");
			final Variable vY = v("Y");
			
			for (final String op : array("+", "-", "*", "/", "%", "<", ">")) {
				if (match($("to_CL", $(vX, op, vY)), e)) {
					autobindTrim("definition_of_" + op + "_to_CL", vX.get(), vY.get());
					
					return;
				}
			}
			
			fail();
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			
			matchOrFail($("to_CL", $("cases", $("", $(vx, "otherwise")))), e);
			
			autobindTrim("definition_of_cases_otherwise_to_CL", vx.get());
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			final Variable vy = v("y");
			final Variable vc = v("c");
			
			matchOrFail($("to_CL", $("cases", $("", $(vx, "if", vc), $("", $(vy, "otherwise"))))), e);
			
			autobindTrim("definition_of_cases_if_otherwise_to_CL", vx.get(), vc.get(), vy.get());
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			
			matchOrFail($("to_CL", $("step_1", vx)), e);
			
			subdeduction();
			
			autobindTrim("definition_of_step_1", vx.get());
			
			rewrite(name(-2), name(-1), 1);
			
			conclude();
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			
			matchOrFail($("to_CL", vx), e);
			
			autobindTrim("definition_of_real_to_CL", vx.get());
		}))
		.simplifyCompletely(expression);
	}
	
}
