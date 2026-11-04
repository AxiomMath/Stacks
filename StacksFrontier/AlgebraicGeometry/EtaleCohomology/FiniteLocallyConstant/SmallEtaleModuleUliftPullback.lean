module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftFunctorSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits

/-!
# The universe lift of module sheaves on a small étale site, against inverse image

Mathlib's small étale site of `X : Scheme.{u}` has objects in `Type (u + 1)` and morphisms in
`Type u`, so its sheaves of `Λ`-modules carry sheafification from the module universe `u + 1` on.
Raising the module universe to `ModuleCat.{max (u + 1) v} Λ` is `CategoryTheory.sheafCompose`
with `ModuleCat.uliftFunctor`. This file shows that this functor is exact and commutes with
inverse image, and identifies the Kan-extension inverse image of
`AlgebraicGeometry.etaleSiteSheafPullbackModule` with the abstract one.

## Main results

* `AlgebraicGeometry.preservesFiniteLimits_sheafCompose_smallEtale_moduleUliftFunctor` and
  `AlgebraicGeometry.preservesFiniteColimits_sheafCompose_smallEtale_moduleUliftFunctor`:
  **raising the module universe of a sheaf on a small étale site is exact.**
* `AlgebraicGeometry.smallEtaleSheafPullbackModuleUliftIso`: **inverse image along a morphism of
  schemes commutes with raising the module universe.**
* `AlgebraicGeometry.etaleSiteSheafPullbackModuleIsoSheafPullback`: the inverse image of
  `AlgebraicGeometry.etaleSiteSheafPullbackModule`, built by a left Kan extension, is the abstract
  left adjoint `CategoryTheory.Functor.sheafPullback` of the same direct image.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
* [Stacks Project, Tag 00WX](https://stacks.math.columbia.edu/tag/00WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u r

namespace AlgebraicGeometry

section Exactness

variable (X : Scheme.{u}) (Λ : Type r) [Ring Λ]

/-- **Raising the module universe of a sheaf on a small étale site preserves finite limits.** -/
theorem preservesFiniteLimits_sheafCompose_smallEtale_moduleUliftFunctor :
    PreservesFiniteLimits
      (sheafCompose X.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ)) := by
  let _ : PreservesLimitsOfSize.{0, 0} (ModuleCat.uliftFunctor.{v, u + 1} Λ) :=
    ModuleCat.uliftFunctor_preservesLimitsOfSize.{v, u + 1, 0, 0, r} Λ
  let _ : PreservesFiniteLimits (ModuleCat.uliftFunctor.{v, u + 1} Λ) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let hpre : PreservesFiniteLimits
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (Functor.whiskeringRight (X.Etale)ᵒᵖ (ModuleCat.{u + 1} Λ)
          (ModuleCat.{max (u + 1) v} Λ)).obj (ModuleCat.uliftFunctor.{v, u + 1} Λ)) :=
    comp_preservesFiniteLimits
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      ((Functor.whiskeringRight (X.Etale)ᵒᵖ (ModuleCat.{u + 1} Λ)
          (ModuleCat.{max (u + 1) v} Λ)).obj (ModuleCat.uliftFunctor.{v, u + 1} Λ))
  let _ : PreservesFiniteLimits
      (sheafCompose X.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ) ⋙
        sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)) := hpre
  exact preservesFiniteLimits_of_reflects_of_preserves
    (sheafCompose X.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ))
    (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ))

/-- **Raising the module universe of a sheaf on a small étale site preserves finite
colimits.** -/
theorem preservesFiniteColimits_sheafCompose_smallEtale_moduleUliftFunctor :
    PreservesFiniteColimits
      (sheafCompose X.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ)) := by
  refine ⟨fun I _ _ ↦ ?_⟩
  let _ : PreservesColimitsOfShape I (ModuleCat.uliftFunctor.{v, u + 1} Λ) :=
    ModuleCat.uliftFunctor_preservesColimitsOfShape.{v, u + 1, 0, 0, r} Λ I
  exact preservesColimitsOfShape_sheafCompose X.smallEtaleTopology
    (ModuleCat.uliftFunctor.{v, u + 1} Λ) I

end Exactness

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type r) [Ring Λ]

/-- The universe lift of modules preserves the colimits computing the presheaf-level left Kan
extension along base change of small étale sites. -/
theorem preservesColimitsOfShape_costructuredArrow_moduleUliftFunctor
    (Z : (X.Etale)ᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow (Stacks.EtaleCohomology.smallEtaleBaseChange f).op Z)
      (ModuleCat.uliftFunctor.{v, u + 1} Λ) :=
  ModuleCat.uliftFunctor_preservesColimitsOfShape.{v, u + 1, u + 1, u, r} Λ _

/-- **Inverse image of sheaves of `Λ`-modules on Mathlib's small étale sites commutes with raising
the module universe.** -/
def smallEtaleSheafPullbackModuleUliftIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullback
          (ModuleCat.{max (u + 1) v} Λ) Y.smallEtaleTopology X.smallEtaleTopology).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ)).obj F) ≅
      (sheafCompose X.smallEtaleTopology (ModuleCat.uliftFunctor.{v, u + 1} Λ)).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullback (ModuleCat.{u + 1} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology).obj F) :=
  letI : ∀ Z : (X.Etale)ᵒᵖ, PreservesColimitsOfShape
      (CostructuredArrow (Stacks.EtaleCohomology.smallEtaleBaseChange f).op Z)
      (ModuleCat.uliftFunctor.{v, u + 1} Λ) :=
    preservesColimitsOfShape_costructuredArrow_moduleUliftFunctor.{v} f Λ
  (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPullbackSheafComposeIso
    (ModuleCat.{u + 1} Λ) Y.smallEtaleTopology X.smallEtaleTopology
    (ModuleCat.uliftFunctor.{v, u + 1} Λ) F

end Pullback

section KanComparison

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) (Λ : Type r) [Ring Λ]

/-- **The inverse image on Mathlib's small étale site is the abstract left adjoint of the direct
image.** The inverse image `AlgebraicGeometry.etaleSiteSheafPullbackModule`, built by a left Kan
extension, is isomorphic to `CategoryTheory.Functor.sheafPullback`. -/
def etaleSiteSheafPullbackModuleIsoSheafPullback :
    etaleSiteSheafPullbackModule B f Λ ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPullback
        (ModuleCat.{u + 1} Λ) X.obj.smallEtaleTopology Y.obj.smallEtaleTopology :=
  (etaleSiteSheafPullbackModuleAdjunction B f Λ).leftAdjointUniq
    (Functor.sheafAdjunctionContinuous _ _ _ _)

end KanComparison

end AlgebraicGeometry

end
