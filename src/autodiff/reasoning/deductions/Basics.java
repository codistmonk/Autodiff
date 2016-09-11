package autodiff.reasoning.deductions;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Stack.*;
import static java.util.Arrays.asList;
import static multij.tools.Tools.*;

import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.Goal;
import multij.rules.Variable;

import java.util.Arrays;
import java.util.Collections;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2015-04-12)
 */
public final class Basics {
	
	private Basics() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(Basics.class, "loaded")) {
			return;
		}
		
		supposeRewrite();
		deduceIdentity();
		deduceCommutativityOfEquality();
		deduceRecall();
		
		{
			final Variable vx = new Variable("x");
			
			Auto.hintAutodeduce(Auto.tryMatch($(vx, "=", vx), (e, m) -> {
				bind("identity", vx.get());
				
				return true;
			}));
		}
	}
	
	public static final void supposeRewrite() {
		final Object p = $new("P");
		final Object q = $new("Q");
		final Object x = $new("X");
		final Object y = $new("Y");
		final Object i = $new("I");
		
		// \/P P -> \/X,Y X=Y -> \/I,Q P|X=Y@[I] = Q -> Q 
		suppose("rewrite", $forall(p, $rule(p,
				$forall(x, $forall(y, $rule($equality(x, y),
						$forall(i, $forall(q, $rule($equality($(p, GIVEN, asList($replacement(x, y)), AT, i), q), q)))))))));
	}
	
	public static final void deduceIdentity() {
		subdeduction("identity");
		
		final Object x = forall("X");
		
		substitute(x, map());
		rewrite(name(-1), name(-1));
		
		conclude();
	}
	
	public static final void rewrite(final String targetName, final String equalityName, final int... indices) {
		rewrite(newName(), targetName, equalityName, indices);
	}
	
	public static final void rewrite(final String propositionName, final String targetName, final String equalityName, final int... indices) {
		subdeduction(propositionName);
		
		final Object target = checkProposition(targetName);
		
		bind("rewrite", target);
		apply(name(-1), targetName);
		
		final Object equality = checkEquality(equalityName);
		
		bind(name(-1), left(equality), right(equality));
		apply(name(-1), equalityName);
		substitute(target, map(left(equality), right(equality)), indices);
		bind(name(-2), indices(indices), right(proposition(-1)));
		apply(name(-1), name(-2));
		
		set(conclude().getMessage(), "By rewriting in", targetName, "using", equalityName, "at",
				Arrays.stream(indices).mapToObj(Integer::valueOf).collect(toTreeSet()));
	}
	
	public static final void deduceCommutativityOfEquality() {
		subdeduction("commutativity_of_equality");
		
		final Object x = forall("X");
		final Object y = forall("Y");
		
		suppose($equality(x, y));
		bind("identity", x);
		rewrite(name(-1), name(-2), 0);
		
		conclude();
	}
	
	public static final void rewriteRight(final String targetName, final String equalityName, final int... indices) {
		rewriteRight(newName(), targetName, equalityName, indices);
	}
	
	public static final void rewriteRight(final String propositionName, final String targetName, final String equalityName, final int... indices) {
		subdeduction(propositionName);
		
		final Object equality = checkEquality(equalityName);
		
		bind("commutativity_of_equality", left(equality), right(equality));
		apply(name(-1), equalityName);
		rewrite(targetName, name(-1), indices);
		
		set(conclude().getMessage(), "By right rewriting in", targetName, "using", equalityName, "at",
				Arrays.stream(indices).mapToObj(Integer::valueOf).collect(toTreeSet()));
	}
	
	public static final void deduceRecall() {
		subdeduction("recall");
		
		final Object x = forall("X");
		
		suppose(x);
		
		bind("identity", x);
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void recall(final String recalledPropositionName) {
		recall(null, recalledPropositionName);
	}
	
	public static final void recall(final String newPropositionName, final String recalledPropositionName) {
		if (newPropositionName != null || !recalledPropositionName.equals(name(-1)) || !deduction().getProofs().containsKey(recalledPropositionName)) {
			subdeduction(newPropositionName == null ? newName() : newPropositionName);
			{
				bind("recall", proposition(recalledPropositionName));
				apply(name(-1), recalledPropositionName);
			}
			conclude();
		}
	}
	
	public static final void simplifyElementaryExpression(final String targetName, final Object expression) {
		subdeduction();
		
		final Object simplified = ElementaryVerification.Evaluator.INSTANCE.apply(expression);
		
		verifyElementaryProposition($(expression, "=", simplified));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final Deduction subbuild(final String deductionName, final Runnable deductionBuilder, final Deduction.Processor printer) {
		return build(new Deduction(deduction(), deductionName), deductionBuilder, printer);
	}
	
	public static final Deduction build(final String deductionName, final Runnable deductionBuilder, final Deduction.Processor printer) {
		return build(new Deduction(null, deductionName), deductionBuilder, printer);
	}
	
	public static final Deduction build(final Deduction deduction, final Runnable deductionBuilder, final Deduction.Processor printer) {
		final Deduction result = push(deduction);
		
		try {
			deductionBuilder.run();
			
			return result.conclude();
		} catch (final Throwable exception) {
			printer.process(deduction());
			
			Deduction d = deduction();
			int n = depth(d);
			
			while (d != null) {
				final Goal activeGoal = Goal.activeGoalFor(d);
				
				if (activeGoal != null) {
					System.out.println();
					System.out.println(Tools.join("", Collections.nCopies(n, "\t")) + "Goal: " + Simple.collapse(activeGoal.getProposition()));
				}
				
				d = d.getParent();
				--n;
			}
			
			return throwUnchecked(exception);
		} finally {
			while (result != pop()) {
				// NOP
			}
		}
	}
	
	public static final int depth(final Deduction deduction) {
		return deduction.getParent() == null ? 0 : 1 + depth(deduction.getParent());
	}
	
}
