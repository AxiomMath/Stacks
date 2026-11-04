module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The higher direct images of `a^{-1}F` along a hypercovering by a simplicial object

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`
and let `a : U ⟶ X` be an augmentation which is a hypercovering of `X` in `C` in the sense of
Stacks 09X8, with augmentation morphism of topoi `a : Sh((C/U)_total) → Sh(C/X)`. Stacks 0D8N
asserts that `E ⟶ Ra_* a^{-1} E` is an isomorphism for every `E` in `D(C/X)`. Read at a single
abelian sheaf `F` in degree zero and in one cohomological degree, it says

`a_* a^{-1} F = F` and `R^q a_* a^{-1} F = 0` for `q > 0`,

that is, `a^{-1}F` is right acyclic for `a_*`. This file records the vanishing, a statement which
mentions no derived category.

## Main results

* `isZero_rightDerived_abelianTotalPushforwardOver_of_isHypercovering`:
  `R^q a_* a^{-1} F = 0` for `q > 0`.

## Implementation notes

The cohomology of `Ra_*` at `F[0]` is Mathlib's classical `R^q a_*` at `F` by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, and `a^{-1}(F[0])` is
`(a^{-1}F)[0]` because `a^{-1}` is exact. The derived categories are those Stacks 0D8N is stated
with; the conclusion does not depend on that choice.

## References

* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The direct image `a_*` along the augmentation of the total site of a simplicial object over
`X` is additive. -/
instance additive_abelianTotalPushforwardOver_associated :
    (abelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)).Additive :=
  additive_abelianTotalPushforwardOver P.toGrothendieck X _

/-- **`R^q a_* a^{-1} F = 0` for `q > 0`, for a hypercovering by a simplicial object of the site.**
Let `a : U ⟶ X` be a hypercovering of `X` in `C` (Stacks 09X8) and `F` an abelian sheaf on `C/X`.
Then the higher direct images of `a^{-1}F` along the augmentation
`a : Sh((C/U)_total) → Sh(C/X)` vanish: this is Stacks 0D8N, `F[0] ≅ Ra_* a^{-1}(F[0])`, read in
cohomological degree `q`. -/
theorem isZero_rightDerived_abelianTotalPushforwardOver_of_isHypercovering
    (h : IsHypercoveringAugmentation P U a) (F : Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})
    (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)).rightDerived q).obj
        ((abelianTotalInverseImageOver P.toGrothendieck X
          (associatedSimplicialObject.{u} U a)).obj F)) := by
  let := HasDerivedCategory.standard (AbelianSheavesOver P.toGrothendieck X)
  let := HasDerivedCategory.standard
    (TotalAbelianSheavesOver P.toGrothendieck X (associatedSimplicialObject.{u} U a))
  have := hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver P.toGrothendieck X
    (associatedSimplicialObject.{u} U a)
  have := additive_abelianTotalInverseImageOver P.toGrothendieck X
    (associatedSimplicialObject.{u} U a)
  have := preservesFiniteColimits_abelianTotalInverseImageOver P.toGrothendieck X
    (associatedSimplicialObject.{u} U a)
  have e₁ := (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (abelianTotalPushforwardOver P.toGrothendieck X (associatedSimplicialObject.{u} U a))
    (derivedAbelianTotalPushforwardOver P.toGrothendieck X (associatedSimplicialObject.{u} U a))
    (derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X
      (associatedSimplicialObject.{u} U a))
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) q).app
      ((abelianTotalInverseImageOver P.toGrothendieck X
        (associatedSimplicialObject.{u} U a)).obj F)
  have e₂ := (((abelianTotalInverseImageOver P.toGrothendieck X
    (associatedSimplicialObject.{u} U a)).mapDerivedCategorySingleFunctor 0).app F).symm
  have hunit := isIso_derivedAugmentationUnitAugmented_app_unconditional P U a h
    ((DerivedCategory.singleFunctor (AbelianSheavesOver P.toGrothendieck X) 0).obj F)
  have e₃ := (asIso ((derivedAugmentationUnitAugmented P U a).app
    ((DerivedCategory.singleFunctor (AbelianSheavesOver P.toGrothendieck X) 0).obj F))).symm
  have hz : IsZero ((DerivedCategory.homologyFunctor (AbelianSheavesOver P.toGrothendieck X)
      (q : ℤ)).obj ((DerivedCategory.singleFunctor
        (AbelianSheavesOver P.toGrothendieck X) 0).obj F)) :=
    DerivedCategory.isZero_of_isLE _ 0 (q : ℤ) (by exact_mod_cast hq)
  exact hz.of_iso (e₁.symm ≪≫ (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
    ((derivedAbelianTotalPushforwardOver P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)).mapIso e₂ ≪≫ e₃))

end CategoryTheory.SimplicialSemiRepresentable

end
