module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseDescent

/-!
# The coefficient universe of a finite locally constant sheaf of sets on a small étale site

Mathlib's small étale site of a scheme `S : Scheme.{u}` has objects in `Type (u + 1)` and
morphisms in `Type u`, so the smallest universe in which its sheaves of sets carry a Yoneda
lemma is `u + 1`, while a statement whose coefficients are modules over a ring in `Type v` has
to present them in `Type (max (u + 1) v)`. On finite locally constant sheaves the two
presentations agree: such a sheaf with sections in `Type (max (u + 1) v)` is the pointwise
universe lift of one with sections in `Type (u + 1)`.

This is `Stacks.ConstantSheaf.exists_isFiniteLocallyConstant_uliftFunctor_iso` at the small
étale site, the sheafification hypotheses it carries being instances there.

## Main results

* `AlgebraicGeometry.exists_isFiniteLocallyConstant_smallEtale_uliftFunctor_iso`: the universe
  descent, from `Type (max (u + 1) v)` to `Type (u + 1)`, of a finite locally constant sheaf of
  sets on the small étale site of a scheme.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03RU](https://stacks.math.columbia.edu/tag/03RU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **A finite locally constant sheaf of sets on the small étale site of a scheme `S : Scheme.{u}`
with sections in `Type (max (u + 1) v)` is the pointwise universe lift of one with sections in
`Type (u + 1)`**, which is again finite locally constant. -/
theorem exists_isFiniteLocallyConstant_smallEtale_uliftFunctor_iso (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type max (u + 1) v))
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology F) :
    ∃ F₀ : Sheaf S.smallEtaleTopology (Type (u + 1)),
      Stacks.ConstantSheaf.IsFiniteLocallyConstant S.smallEtaleTopology F₀ ∧
        Nonempty ((sheafCompose S.smallEtaleTopology
          uliftFunctor.{v, u + 1}).obj F₀ ≅ F) :=
  Stacks.ConstantSheaf.exists_isFiniteLocallyConstant_uliftFunctor_iso.{v, u, u + 1}
    S.smallEtaleTopology F hF

end AlgebraicGeometry

end
