package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.expressions.Expressions.$;
import static autodiff.reasoning.expressions.Expressions.$forall;
import static autodiff.reasoning.expressions.Expressions.$new;
import static autodiff.reasoning.expressions.Expressions.$rule;
import static autodiff.reasoning.expressions.Expressions.LNOT;
import static autodiff.reasoning.expressions.Expressions.condition;
import static autodiff.reasoning.expressions.Expressions.second;
import static autodiff.reasoning.proofs.Stack.abort;
import static autodiff.reasoning.proofs.Stack.apply;
import static autodiff.reasoning.proofs.Stack.bind;
import static autodiff.reasoning.proofs.Stack.conclude;
import static autodiff.reasoning.proofs.Stack.forall;
import static autodiff.reasoning.proofs.Stack.name;
import static autodiff.reasoning.proofs.Stack.proposition;
import static autodiff.reasoning.proofs.Stack.subdeduction;
import static autodiff.reasoning.proofs.Stack.suppose;
import static autodiff.reasoning.proofs.Stack.verifyElementaryProposition;
import static multij.tools.Tools.append;
import static multij.tools.Tools.array;
import static multij.tools.Tools.debugPrint;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class Cases {
	
	private Cases() {
		throw new IllegalInstantiationException();
	}
	
	public static final void setup() {
		supposeEliminationsOfCases();
		testEliminationOfCases();
	}
	
	public static final void supposeEliminationsOfCases() {
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

	public static final void testEliminationOfCases() {
		{
			subdeduction("try_cases.test1");
			
			final Object _x = forall("x");
			
			suppose($(_x, "=", cases(
					$(42, "if", $(2, "=", 2)),
					$(24, "otherwise"))));
			
			{
				subdeduction();
				
				bind("try_cases_if_stop", 42, $("", $(24, "otherwise")), $(2, "=", 2));
				verifyElementaryProposition($(2, "=", 2));
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
					verifyElementaryProposition($(2, "=", 3));
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
					verifyElementaryProposition($(1, "=", 2));
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
	
	public static final Object cases(final Object... cases) {
		return Sequences.sequence("", append(array((Object) "cases"), cases));
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
			
			verifyElementaryProposition(formula);
			
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
	
}
