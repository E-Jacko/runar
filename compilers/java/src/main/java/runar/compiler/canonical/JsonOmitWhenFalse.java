package runar.compiler.canonical;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks a {@code boolean} record component as omitted from the JSON output
 * when its value is {@code false}. Used by optional marker fields whose
 * absence is the default and whose presence carries semantic meaning
 * (e.g. {@link runar.compiler.ir.anf.Assert#isAutoInjectedStateCheck()}).
 *
 * <p>This preserves byte-identical conformance output for the common case
 * where the marker is not set, matching the JSON-omit-when-default
 * semantics used by the other compiler tiers' encoders.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.RECORD_COMPONENT)
public @interface JsonOmitWhenFalse {
}
