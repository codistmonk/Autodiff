package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Basics.rewriteRight;
import static autodiff.reasoning.deductions.Sequences.sequence;
import static autodiff.reasoning.deductions.Sets.justicationFor;
import static autodiff.reasoning.deductions.Sets.p;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.N;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.reasoning.tactics.Stack.*;

import autodiff.reasoning.tactics.Stack.PropositionDescription;

import java.io.Serializable;

import multij.rules.Rules;
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
	
	/**
	 * @author codistmonk (creation 2016-08-18)
	 */
	public static final class ToCLHelper implements Serializable {
		
		private final Rules<Object, Void> rules = new Rules<>();
		
		{
			{
				final Variable vX = v("X");
				final Variable vi = v("i");
				final Variable vn = v("n");
				
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
				final Variable vX = v("X");
				
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
	
}
