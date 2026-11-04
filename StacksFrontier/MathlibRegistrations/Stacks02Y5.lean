module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Fibres

/-! Stacks tag 02Y5 is proved in
`StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Fibres`, which this module
re-exports.

The routing that formerly stood here, onto `CategoryTheory.Limits.CategoricalPullback`, was
incorrect: `CategoricalPullback` is the 2-fibre product of *plain* categories (Stacks 003R), whose
comparison isomorphisms need not be vertical over the base, whereas Stacks 02Y5 describes the
fibre category of the 2-fibre product *over `𝒞`* (Stacks 0040) — the two are inequivalent, and
the fibre category of the former is not the category the tag describes. -/
