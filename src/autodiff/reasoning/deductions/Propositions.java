package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Stack.*;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-27)
 */
public final class Propositions {
	
	private Propositions() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		supposeLeftEliminationOfDisjunction();
		supposeRightEliminationOfDisjunction();
		supposeIntroductionOfConjunction();
		supposeLeftEliminationOfConjunction();
		supposeRightEliminationOfConjunction();
		supposeDefinitionOfLogicalEquivalence();
		supposeLogicalEquality();
		deduceLogicalEquivalenceImpliesLogicalEquality();
		deduceCommutativityOfConjunction();
	}
	
	public static final void supposeLeftEliminationOfDisjunction() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		final Object _Z = $new("Z");
		
		suppose("left_elimination_of_disjunction",
				$forall(_X, _Y, _Z,
						$rule($rule($(_X, LOR, _Y), _Z), _X, _Z)));
	}
	
	public static final void supposeRightEliminationOfDisjunction() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		final Object _Z = $new("Z");
		
		suppose("right_elimination_of_disjunction",
				$forall(_X, _Y, _Z,
						$rule($rule($(_X, LOR, _Y), _Z), _Y, _Z)));
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
	
}
