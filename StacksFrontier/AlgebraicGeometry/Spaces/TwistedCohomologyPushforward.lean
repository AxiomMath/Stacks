module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAcyclicPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleTwistExact
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward

/-!
# Twisted cohomology of a direct image with no higher direct images

Let `g : X ⟶ V` be a morphism of algebraic spaces over `Spec A` to an object `V` of the site,
`h : Y ⟶ X` a morphism, `L₁, …, L_r` invertible `𝒪_X`-modules and `𝒩` an `𝒪_Y`-module whose
higher direct images along `h` vanish.  Then for every integral tuple `n` and every degree `i`

`H^i(X, h_*𝒩 ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}) ≅ H^i(Y, 𝒩 ⊗ h^*L₁^{⊗ n₁} ⊗ ⋯ ⊗ h^*L_r^{⊗ n_r})`

as `A`-modules.  The twist moves through the direct image by the projection formula
(`AlgebraicGeometry.Space.modulePushforwardTwistedModuleIso`), the twisted module has no higher
direct images because twisting commutes with them
(`AlgebraicGeometry.Space.rightDerivedModulePushforwardTwistedModuleIso`) and carries zero to
zero, and the Leray collapse `AlgebraicGeometry.Space.cohomologyRestrictScalarsIsoOfAcyclic`
applies.  This is the computation in the second proof of condition (3) of the source's proof of
Stacks 0DN4.

## Main results

* `AlgebraicGeometry.Space.isZero_twistedModule_of_isZero`: a twist of a zero module is zero.
* `AlgebraicGeometry.Space.twistedCohomologyRestrictScalarsIsoOfAcyclic`: the isomorphism above.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

/-- **A twist of a zero module is zero**: twisting is an autoequivalence
(`AlgebraicGeometry.Space.isEquivalence_twistedModuleExactFunctor`). -/
theorem isZero_twistedModule_of_isZero (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {r : ℕ} (L : Fin r → Modules.{u, u} B S hS F hF)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property (L j)]
    (n : Fin r → ℤ) {M : Modules.{u, u} B S hS F hF} (hM : IsZero M) :
    IsZero (twistedModule B S hS F hF M L n) := by
  rw [← twistedModuleExactFunctor_obj]
  exact Functor.map_isZero _ hM

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
    (V : BigFppfOver B (Spec (.of A)) hA)

/-- **The twisted cohomology of a direct image with no higher direct images**: for `h : Y ⟶ X`
and an `𝒪_Y`-module `𝒩` with `R^q h_*𝒩 = 0` for `q > 0`,
`H^i(X, h_*𝒩 ⊗ L^{⊗ n}) ≅ H^i(Y, 𝒩 ⊗ (h^*L)^{⊗ n})` as `A`-modules, in every degree. -/
def twistedCohomologyRestrictScalarsIsoOfAcyclic {X Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (g : X ⟶ (schemeSpace V :
      AlgebraicSpaces B (Spec (.of A)) hA)) (h : Y ⟶ X) {r : ℕ}
    (L : Fin r → Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of A)) hA X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O).property (L j)]
    (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (hN : ∀ q, 0 < q →
      have := hasInjectiveResolutions_modules B (Spec (.of A)) hA Y.1 Y.2
      IsZero (((modulePushforward B (Spec (.of A)) hA h).rightDerived q).obj N))
    (n : Fin r → ℤ) (i : ℕ) :
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of A)) hA h (L j)
    (ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived i).obj
          (twistedModule B (Spec (.of A)) hA X.1 X.2
            ((modulePushforward B (Spec (.of A)) hA h).obj N) L n)) ≅
      (ModuleCat.restrictScalars (baseRingHom A B hA Y.1 Y.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA Y.1 Y.2).O)).rightDerived i).obj
          (twistedModule B (Spec (.of A)) hA Y.1 Y.2 N
            (fun j => (modulePullback B (Spec (.of A)) hA h).obj (L j)) n)) :=
  haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of A)) hA h (L j)
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA Y.1 Y.2
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X.1 X.2
  (ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).mapIso
      (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived i).mapIso
        (modulePushforwardTwistedModuleIso B (Spec (.of A)) hA h L n N).symm) ≪≫
    cohomologyRestrictScalarsIsoOfAcyclic V g h _
      (fun q hq => (isZero_twistedModule_of_isZero B (Spec (.of A)) hA X.1 X.2 L n
        (hN q hq)).of_iso
          (rightDerivedModulePushforwardTwistedModuleIso B (Spec (.of A)) hA h L n q N)) i

end AlgebraicGeometry.Space

end
