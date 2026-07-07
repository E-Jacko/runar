"""Parser dispatch — routes source files to the appropriate format parser."""

from __future__ import annotations
import re
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from runar_compiler.frontend.ast_nodes import ContractNode

from runar_compiler.frontend.diagnostic import Diagnostic, Severity


# Author-facing comment directive still fail-closed here: ``@sighash <FLAGS>``
# (#123, per-method sighash type). ``@embedAlways`` (#109) is now supported by
# the Python TS-surface parser, so it is no longer guarded. Word-boundary
# anchored to mirror the TS ``/@sighash\b/`` scan so an identifier like
# ``sighashType`` does not trip the guard.
_SIGHASH_DIRECTIVE_RE = re.compile(r"@sighash\b")


def _unsupported_directive_error(source: str) -> str | None:
    """Return a fail-closed diagnostic message when ``source`` carries a
    directive this compiler does not yet honour, else ``None``. The Python
    frontend ignores comments, so silently dropping the ``@sighash`` directive
    would change signing semantics — reject rather than diverge until the port
    lands.
    """
    if _SIGHASH_DIRECTIVE_RE.search(source):
        return (
            "@sighash directive is not yet supported by the Python compiler "
            "(issue #123); compile the contract with the TypeScript compiler"
        )
    return None


class ParseResult:
    __slots__ = ("contract", "errors")

    def __init__(self, contract: ContractNode | None = None, errors: list[Diagnostic] | None = None):
        self.contract = contract
        self.errors = errors or []

    def error_strings(self) -> list[str]:
        """Return formatted error messages as plain strings."""
        return [d.format_message() for d in self.errors]


def parse_source(source: str, file_name: str) -> ParseResult:
    """Dispatch to the appropriate parser based on file extension."""
    # DoS-bound size guard. Reject oversized source BEFORE any
    # format-specific parser touches the input. Raises
    # :class:`SourceSizeExceededError` on rejection. BUG-008 follow-up.
    from runar_compiler.frontend.input_limits import assert_source_bytes_under_limit
    assert_source_bytes_under_limit(source)

    directive_error = _unsupported_directive_error(source)
    if directive_error is not None:
        return ParseResult(errors=[Diagnostic(
            message=directive_error,
            severity=Severity.ERROR,
        )])

    lower = file_name.lower()

    if lower.endswith(".runar.py"):
        from runar_compiler.frontend.parser_python import parse_python
        return parse_python(source, file_name)
    elif lower.endswith(".runar.ts"):
        from runar_compiler.frontend.parser_ts import parse_ts
        return parse_ts(source, file_name)
    elif lower.endswith(".runar.sol"):
        from runar_compiler.frontend.parser_sol import parse_sol
        return parse_sol(source, file_name)
    elif lower.endswith(".runar.move"):
        from runar_compiler.frontend.parser_move import parse_move
        return parse_move(source, file_name)
    elif lower.endswith(".runar.go"):
        from runar_compiler.frontend.parser_go import parse_go
        return parse_go(source, file_name)
    elif lower.endswith(".runar.rs"):
        from runar_compiler.frontend.parser_rust import parse_rust
        return parse_rust(source, file_name)
    elif lower.endswith(".runar.rb"):
        from runar_compiler.frontend.parser_ruby import parse_ruby
        return parse_ruby(source, file_name)
    elif lower.endswith(".runar.zig"):
        from runar_compiler.frontend.parser_zig import parse_zig
        return parse_zig(source, file_name)
    elif lower.endswith(".runar.java"):
        from runar_compiler.frontend.parser_java import parse_java
        return parse_java(source, file_name)
    else:
        return ParseResult(errors=[Diagnostic(
            message=f"unsupported file extension: {file_name}",
            severity=Severity.ERROR,
        )])
