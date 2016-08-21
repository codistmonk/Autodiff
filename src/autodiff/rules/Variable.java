package autodiff.rules;

import static multij.tools.Tools.cast;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

/**
 * @author codistmonk (creation 2015-12-07)
 */
public final class Variable implements Serializable {
	
	private final String name;
	
	private Object value;
	
	public Variable() {
		this("" + nextId.getAndIncrement());
	}
	
	public Variable(final String name) {
		this.name = name;
	}
	
	public final Object get() {
		return this.value;
	}
	
	public final Variable set(final Object value) {
		this.value = value;
		
		return this;
	}
	
	@Override
	public final String toString() {
		return this.name;
	}
	
	private static final long serialVersionUID = 8910318061831953418L;
	
	private static final AtomicLong nextId = new AtomicLong(1L);
	
	public static final void matchOrFail(final Object pattern, final Object target) {
		if (!match(pattern, target)) {
			throw new IllegalArgumentException("Failed to match " + pattern + " with " + target);
		}
	}
	
	public static final boolean match(final Object pattern, final Object target) {
		return match(pattern, target, new HashMap<>());
	}
	
	public static final boolean match(final Object pattern, final Object target, final Map<Variable, Object> mapping) {
		final Variable variable = cast(Variable.class, pattern);
		
		if (variable != null) {
			final Object existing = mapping.get(variable);
			
			if (existing == null) {
				mapping.put(variable, target);
				
				variable.set(target);
				
				return true;
			}
			
			return existing.equals(target);
		}
		
		final List<?> patternList = cast(List.class, pattern);
		final List<?> targetList = cast(List.class, target);
		
		if (patternList != null && targetList != null) {
			final int n = patternList.size();
			
			if (n != targetList.size()) {
				return false;
			}
			
			for (int i = 0; i < n; ++i) {
				if (!match(patternList.get(i), targetList.get(i), mapping)) {
					return false;
				}
			}
			
			return true;
		}
		
		return pattern.equals(target);
	}
	
	public static final Object rewrite(final Object target, final Map<?, Object> mapping) {
		final Object replacement = mapping.get(target);
		
		if (replacement != null) {
			return replacement;
		}
		
		final List<?> targetList = cast(List.class, target);
		
		if (targetList != null) {
			final int n = targetList.size();
			List<Object> newList = null;
			
			for (int i = 0; i < n; ++i) {
				final Object object = targetList.get(i);
				final Object newObject = rewrite(object, mapping);
				
				if (object != newObject && newList == null) {
					newList = new ArrayList<>(targetList.size());
					newList.addAll(targetList.subList(0, i));
				}
				
				if (newList != null) {
					newList.add(newObject);
				}
			}
			
			if (newList != null) {
				return newList;
			}
		}
		
		return target;
	}
	
}