package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;

import java.util.Arrays;
import java.util.List;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class Binding extends Proof.Abstract {
	
	private final String blockName;
	
	private Object value;
	
	public Binding(final String blockName, final Object value) {
		this(null, blockName, value);
	}
	
	public Binding(final String provedPropositionName, final String blockName, final Object value) {
		super(provedPropositionName, Arrays.asList("By binding", blockName, "with", value));
		this.blockName = blockName;
		this.value = value;
	}
	
	public final String getBlockName() {
		return this.blockName;
	}
	
	public final Object getValue() {
		return this.value;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final List<Object> block = list(checkBlock(this.getBlockName(), context));
		
		return Substitution.substituteIn(scope(block), map(variable(block), this.getValue()), indices());
	}
	
	private static final long serialVersionUID = 5987805106367286343L;
	
}