# Changelog

Main changes to the paper since the OOPSLA 2026 submission (tag
`oopsla-2026-initial`). A visual diff can be generated with
`./make-diff.sh`.

- **Skolem terms instead of skolem types (§4.2).** (4bb4920) The implementation
  no longer reuses Scala's built-in skolem types; it now uses its own custom
  skolem terms in predicates. The "Hoisting and skolems" section was reworded
  accordingly.
- **Fixed a miscitation in related work (§5).** (37883cb) Paraskevopoulou et al.
  use an interpreter-based approach with step-indexed logical relations for
  multi-pass compiler verification; the previous text misattributed the
  combination of definitional interpreters with semantic typing to them.
- **Clarified the depth-bounded interpreter (§3.2).** (b0bc60f) The fuel
  parameter bounds the *depth* of evaluation, not the total number of steps:
  when evaluating an application, the function, the argument, and the body are
  all evaluated with the same, decremented fuel. The previous prose incorrectly
  suggested that fuel is decremented only for the body, and the listing did not
  decrement the fuel at all.
- **Typos and smaller fixes** addressing individual reviewer comments.
