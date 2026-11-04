module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections

/-!
# Vanishing of cohomology along a closed immersion

Let `i : E ⟶ X` be a closed immersion of schemes and `G` a sheaf of modules on `E`. The
cohomology of the direct image `i_* G` on `X` vanishes in a degree exactly when the cohomology
of `G` on `E` vanishes in that degree:

`Hⁿ(X, i_* G) = 0 ↔ Hⁿ(E, G) = 0`.

The comparison itself is `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`, which
identifies the two sides after restriction of scalars along `i^♯ : Γ(X, ⊤) ⟶ Γ(E, ⊤)`. What is
added here is that the restriction of scalars may be dropped from a *vanishing* statement, and
that the two sides are written with `Stacks.Cohomology.sectionsFunctor`, the spelling of global
sections whose right derived functors the vanishing hypotheses of this development use.

Restriction of scalars along a ring homomorphism is additive, so it carries a zero object to a
zero object, and faithful, so it reflects one; both directions of the equivalence are therefore
free. No quasi-coherence, properness or Noetherian hypothesis appears, and the sheaf of modules
is arbitrary: a closed immersion has exact direct image, which is what makes the comparison hold
for every module.

## Main results

* `Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_sectionsFunctor_pushforward_iff`: the
  equivalence above, in every degree.
* `Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_one_sectionsFunctor_pushforward`:
  **`H¹(E, G) = 0` implies `H¹(X, i_* G) = 0`.**

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ClosedImmersion

/-- **Cohomology vanishes along a closed immersion exactly when it vanishes upstairs.** For a
closed immersion `i : E ⟶ X` and a sheaf of modules `G` on `E`, the group `Hⁿ(X, i_* G)` is zero
if and only if `Hⁿ(E, G)` is. -/
theorem isZero_rightDerived_sectionsFunctor_pushforward_iff {E X : Scheme.{u}} (i : E ⟶ X)
    [IsClosedImmersion i] (G : E.Modules) (n : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived n).obj
        ((Scheme.Modules.pushforward i).obj G)) ↔
      IsZero (((Stacks.Cohomology.sectionsFunctor E ⊤).rightDerived n).obj G) := by
  have _ : (ModuleCat.restrictScalars.{u} i.appTop.hom).Additive := ⟨by intros; rfl⟩
  refine (cohomologyObjIsoPushforward i G n).isZero_iff.trans ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsZero.iff_id_eq_zero]
    refine (ModuleCat.restrictScalars i.appTop.hom).map_injective ?_
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 h
  · exact CategoryTheory.Functor.map_isZero _ h

/-- **The first cohomology of a direct image along a closed immersion vanishes with the first
cohomology upstairs.** For a closed immersion `i : E ⟶ X` and a sheaf of modules `G` on `E`,
`H¹(E, G) = 0` implies `H¹(X, i_* G) = 0`. -/
theorem isZero_rightDerived_one_sectionsFunctor_pushforward {E X : Scheme.{u}} (i : E ⟶ X)
    [IsClosedImmersion i] (G : E.Modules)
    (h : IsZero (((Stacks.Cohomology.sectionsFunctor E ⊤).rightDerived 1).obj G)) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj
      ((Scheme.Modules.pushforward i).obj G)) :=
  (isZero_rightDerived_sectionsFunctor_pushforward_iff i G 1).2 h

end Stacks.Cohomology.ClosedImmersion

end
