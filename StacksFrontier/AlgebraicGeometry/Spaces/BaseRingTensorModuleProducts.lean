module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitComparisonHomBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleInverseLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTowerSupplement

/-!
# Countable products of quasi-coherent modules in `D(𝒪_X)`, and the product step of Stacks 0D3F

Let `X` be an algebraic space over a scheme `S`.  A quasi-coherent `𝒪_X`-module has no higher
cohomology on an affine étale chart, and those charts cover the small étale site of `X`; so the
product of a countable family of quasi-coherent modules, placed in degree zero, is the product of
the family in `D(𝒪_X)`: the ordinary product is the derived product.

In the proof of Stacks 0D3F this identifies, for `Φ = 𝒪_X ⊗_R -` and a test object `P` of
`D(𝒪_X)`, the maps `P ⟶ ∏ Φ(M_n)` with the families of maps `P ⟶ Φ(M_n)`.  The hypothesis `hP` of
`CategoryTheory.Limits.bijective_comp_single_limitComparison` thus becomes the statement that
`M ↦ Hom(P[k], Φ(M))` carries the countable product `∏ M_n` to the product of the
`Hom(P[k], Φ(M_n))`.

## Main results

* `AlgebraicGeometry.Space.preservesLimit_singleFunctor_of_isQuasicoherentOnSite`: placing modules
  in degree zero preserves a countable product of quasi-coherent `𝒪_X`-modules.
* `AlgebraicGeometry.Space.bijective_comp_single_piComparison_baseRingTensorModule`: for
  `Φ = 𝒪_X ⊗_R -`, composition with the product comparison `Φ(∏ M_n) ⟶ ∏ Φ(M_n)` in degree zero
  is bijective on maps out of `Y` as soon as the maps `Y ⟶ Φ(∏ M_n)` are the families of maps
  `Y ⟶ Φ(M_n)`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0BKY](https://stacks.math.columbia.edu/tag/0BKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck CategoryTheory.Limits.hasProduct_comp_obj

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A countable product of quasi-coherent `𝒪_X`-modules is a derived product.** Placing
`𝒪_X`-modules in degree zero preserves the product of a countable family of quasi-coherent
modules: such modules have no higher cohomology on affine étale charts (the étale analogue of
Stacks 01XB), and the affine étale charts cover the small étale site of `X`, so the product of
injective resolutions resolves the product (Stacks 0BKY). -/
theorem preservesLimit_singleFunctor_of_isQuasicoherentOnSite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : ℕ → Modules.{u, u} B S hS F hF) (hM : ∀ n, (M n).IsQuasicoherentOnSite) :
    PreservesLimit (Discrete.functor M)
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0) :=
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  Stacks.Cohomology.SiteInverseLimits.preservesLimit_singleFunctor_of_acyclic_cover.{u + 1, u, u,
      u, u}
    (smallEtaleRingedSite B S hS F hF) M (IsAffineChart B S hS F)
    (hasEnoughObjects_isAffineChart B S hS F)
    (fun U hU n p hp ↦
      isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS F hF (M n) (hM n) U hU p hp)

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The product step of the proof of Stacks 0D3F.** Let `Φ = 𝒪_X ⊗_R -` and let `(M_n)` be a
countable family of `R`-modules.  Since `∏ Φ(M_n)` in degree zero is the product of the `Φ(M_n)`
in degree zero in `D(𝒪_X)`, composition with the product comparison `Φ(∏ M_n) ⟶ ∏ Φ(M_n)`, placed
in degree zero, is bijective on maps out of `Y` once every family of maps `Y ⟶ Φ(M_n)` in degree
zero comes from exactly one map `Y ⟶ Φ(∏ M_n)` by composing with the images of the
projections. -/
theorem bijective_comp_single_piComparison_baseRingTensorModule
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    [HasProduct fun n : ℕ => (baseRingTensorModule B S hS X φ).obj (M.obj ⟨n⟩)]
    (Y : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hY : Function.Bijective
      (fun a : Y ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X φ).obj (∏ᶜ fun n : ℕ => M.obj ⟨n⟩)) =>
        fun n : ℕ => a ≫ (DerivedCategory.singleFunctor _ 0).map
          ((baseRingTensorModule B S hS X φ).map (Pi.π (fun n : ℕ => M.obj ⟨n⟩) n)))) :
    Function.Bijective
      (fun a : Y ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X φ).obj (∏ᶜ fun n : ℕ => M.obj ⟨n⟩)) =>
        a ≫ (DerivedCategory.singleFunctor _ 0).map
          (piComparison (baseRingTensorModule B S hS X φ) (fun n : ℕ => M.obj ⟨n⟩))) :=
  have := preservesLimit_singleFunctor_of_isQuasicoherentOnSite B S hS X.1 X.2
    (fun n : ℕ => (baseRingTensorModule B S hS X φ).obj (M.obj ⟨n⟩))
    (fun _n => isQuasicoherentOnSite_baseRingTensorModule B S hS X φ _)
  bijective_comp_single_piComparison (baseRingTensorModule B S hS X φ) M Y hY

end AlgebraicGeometry.Space

end
