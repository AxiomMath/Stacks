module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Comma.Arrow
public import StacksCore.Tactic.StacksAttribute

/-!
# Thickenings of schemes

A *thickening* of a scheme `X` is a closed immersion `i : X ⟶ X'` whose underlying map of
topological spaces is surjective, so that `X` and `X'` have the same points and `X` is cut out
by a sheaf of ideals supported nowhere. The order of a thickening measures the nilpotence of
that sheaf of ideals: the thickening is of order `n` when the `(n+1)`st power of the kernel
ideal sheaf vanishes, and of finite order when some power of it vanishes.

## Main definitions

* `Stacks.Thickenings.IsThickening` is the condition that a closed immersion be surjective on
  points.
* `Stacks.Thickenings.IsFirstOrderThickening` is the condition that a closed immersion have
  square-zero kernel ideal sheaf.
* `Stacks.Thickenings.IsFiniteOrderThickening` is the condition that a closed immersion have
  nilpotent kernel ideal sheaf.
* `Stacks.Thickenings.IsNthOrderThickening` is the condition that a closed immersion have
  kernel ideal sheaf whose `(n+1)`st power vanishes.

## Main results

* `Stacks.Thickenings.isThickening_of_ker_pow_eq_bot`: a closed immersion with nilpotent kernel
  ideal sheaf is a thickening.
* `Stacks.Thickenings.IsFirstOrderThickening.isThickening`,
  `Stacks.Thickenings.IsFiniteOrderThickening.isThickening` and
  `Stacks.Thickenings.IsNthOrderThickening.isThickening` are the three resulting corollaries.

## Implementation notes

The closed subscheme is represented by its closed immersion rather than as a subobject, and its
defining sheaf of ideals is `AlgebraicGeometry.Scheme.Hom.ker`, an ideal sheaf on the ambient
scheme. The order conditions are therefore equations between ideal sheaves, and the surjectivity
in `Stacks.Thickenings.isThickening_of_ker_pow_eq_bot` is deduced from them by comparing
supports: the support of the kernel is the closure of the range of the immersion, and the
support of a positive power of an ideal sheaf agrees with the support of the ideal sheaf itself.

Morphisms of thickenings, parts (5) and (6) of the tag, are commutative squares, that is
morphisms in the arrow category `CategoryTheory.Arrow` of `AlgebraicGeometry.Scheme` — and, for
thickenings over a fixed base `S`, morphisms in the arrow category of `CategoryTheory.Over S`.
No new definition is needed for them, so they are recorded on `CategoryTheory.Arrow.Hom` by
`add_to_stacks`.

All four predicates are abbreviations, so that a client can apply the underlying conjunction
directly without an intervening projection lemma.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-- A **thickening** is a closed immersion `i : X ⟶ X'` whose underlying map of topological
spaces is surjective, so that the closed subscheme `X` and the ambient scheme `X'` have the
same underlying topological space. -/
@[stacks 04EX "part (1): thickening"]
abbrev IsThickening {X X' : Scheme.{u}} (i : X ⟶ X') : Prop :=
  IsClosedImmersion i ∧ Function.Surjective i

/-- A **first-order thickening** is a closed immersion whose kernel ideal sheaf is
square-zero. -/
@[stacks 04EX "part (2): first-order thickening"]
abbrev IsFirstOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ 2 = ⊥

/-- A **finite-order thickening** is a closed immersion whose kernel ideal sheaf is
nilpotent. -/
@[stacks 04EX "part (3): finite-order thickening"]
abbrev IsFiniteOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X') : Prop :=
  IsClosedImmersion i ∧ ∃ n : ℕ, i.ker ^ (n + 1) = ⊥

/-- An **`n`th-order thickening** is a closed immersion whose kernel ideal sheaf has vanishing
`(n+1)`st power. -/
@[stacks 04EX "part (4): nth-order thickening"]
abbrev IsNthOrderThickening {X X' : Scheme.{u}} (n : ℕ) (i : X ⟶ X') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥

/-- A closed immersion whose kernel ideal sheaf has a vanishing positive power is a thickening:
the support of the kernel is the closure of the range of the immersion, which is the range
itself because a closed immersion is a closed embedding, and the support of a positive power of
an ideal sheaf is the support of that ideal sheaf. -/
theorem isThickening_of_ker_pow_eq_bot {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsClosedImmersion i) {n : ℕ} (hn : i.ker ^ (n + 1) = ⊥) :
    IsThickening i := by
  refine ⟨hi, ?_⟩
  rw [← Set.range_eq_univ, ← i.isClosedEmbedding.isClosed_range.closure_eq,
    ← Scheme.Hom.support_ker]
  simpa only [Scheme.IdealSheafData.support_pow_succ,
    Scheme.IdealSheafData.support_bot, TopologicalSpace.Closeds.coe_top] using
    congrArg (fun J : X'.IdealSheafData => (J.support : Set X')) hn

/-- A first-order thickening is a thickening: the closed subscheme and the ambient scheme have
the same underlying topological space. -/
theorem IsFirstOrderThickening.isThickening {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsFirstOrderThickening i) : IsThickening i :=
  isThickening_of_ker_pow_eq_bot i hi.1 (by simpa using hi.2)

/-- A finite-order thickening is a thickening: the closed subscheme and the ambient scheme have
the same underlying topological space. -/
theorem IsFiniteOrderThickening.isThickening {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsFiniteOrderThickening i) : IsThickening i :=
  isThickening_of_ker_pow_eq_bot i hi.1 hi.2.choose_spec

/-- An `n`th-order thickening is a thickening: the closed subscheme and the ambient scheme have
the same underlying topological space. -/
theorem IsNthOrderThickening.isThickening {X X' : Scheme.{u}} {i : X ⟶ X'}
    {n : ℕ} (hi : IsNthOrderThickening n i) : IsThickening i :=
  isThickening_of_ker_pow_eq_bot i hi.1 hi.2

add_to_stacks 04EX "parts (5) and (6): morphisms of thickenings, also over a base"
  CategoryTheory.Arrow.Hom

end Stacks.Thickenings

end
