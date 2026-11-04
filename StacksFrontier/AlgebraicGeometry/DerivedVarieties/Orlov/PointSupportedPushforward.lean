module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ZeroDimensionalTransform
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointSupportDecomposition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxHomVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional

/-!
# Direct images of complexes supported over an affine open

Let `𝓕` be a quasi-coherent module on a scheme `X` supported on a closed subset `Z` of an affine
open `U`, and let `f : X ⟶ S` with `U ⟶ S` affine (for instance `S` affine). For `K ∈ D(𝒪_X)`
with quasi-coherent cohomology in degrees `≤ a`, the direct image `Rf_*(𝓕[0] ⊗^𝐋 K)` lies in
degrees `≤ a`: the derived tensor product is supported on `Z`, and over `U` the morphism is
affine, so its direct image has no higher cohomology there.

For `S = Spec k` and `K = ℰ[0]` with `ℰ` finite locally free this says that
`Rf_*(𝓕 ⊗ ℰ) = Γ(X, 𝓕 ⊗ ℰ)` is concentrated in degree `0`, which is the identification
`R pr_{2,*}((𝓕 ⊗ ℰᵢ) ⊠ 𝒢) = Γ(X, 𝓕 ⊗ ℰᵢ) ⊗_k 𝒢` of [Stacks, Section 0G07] for a coherent module
supported at a closed point.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_singleFunctor_of_supp`: a module supported on `Z`,
  placed in degree zero, has cohomology supported on `Z`.
* `AlgebraicGeometry.isZero_homology_dpush_dtenR_of_supp`: the vanishing above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **A module supported on `Z`, placed in degree zero, has cohomology supported on `Z`.** -/
theorem cohomologySupportedOn_singleFunctor_of_supp (𝓕 : X.Modules) {Z : Set X}
    (h𝓕 : SheafOfModules.supp 𝓕 ⊆ Z) :
    AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.toRingedSpace.sheaf) Z
      ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕) := by
  intro i x hx
  refine (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ x _).1 ?_
  by_cases hi : i = 0
  · subst hi
    exact ((notMem_supp_iff_isZero_stalkFunctor X.ringCatSheaf 𝓕 x).1 fun hm => hx (h𝓕 hm)).of_iso
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app 𝓕))
  · have hz : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)) := by
      rcases lt_or_gt_of_ne hi with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i h
    exact Functor.map_isZero (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x) hz

/-- **`Rf_*(𝓕[0] ⊗^𝐋 K)` lies in degrees `≤ a`** when `𝓕` is quasi-coherent and supported on a
closed subset of an open `U` over which `f` is affine, and `K` has quasi-coherent cohomology in
degrees `≤ a`. -/
theorem isZero_homology_dpush_dtenR_of_supp {S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    [IsAffineHom (U.ι ≫ f)] {Z : Set X} (hZ : IsClosed Z) (hZU : Z ⊆ U) (𝓕 : X.Modules)
    (h𝓕 : SheafOfModules.supp 𝓕 ⊆ Z) (h𝓕qc : 𝓕.IsQuasicoherent) (K : DerivedCategory X.Modules)
    (hK : IsQCohAll K) (a : ℤ) (ha : K.IsLE a) (i : ℤ) (hi : a < i) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules i).obj ((dpush f).obj
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)).obj K))) := by
  let A := (DerivedCategory.singleFunctor X.Modules 0).obj 𝓕
  have hA : A.IsLE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕).IsLE 0)
  have hE : (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj A).obj K).IsLE (0 + a) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor _ _ _
      X.toRingedSpace.sheaf _ _ _ _ _ _ _ _ 0 a hA ha
  rw [zero_add] at hE
  have hsupp := Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left
    X.toRingedSpace.sheaf Z A K (cohomologySupportedOn_singleFunctor_of_supp 𝓕 h𝓕)
  open Stacks.AlgebraicGeometry.SupportedPushforwardReflect in
  exact isZero_homology_derivedPushforward_of_supported f U hZ hZU _ hsupp
    (TorFormula.isQuasicoherent_homology_derivedTensor X A K
      (isQuasicoherent_homology_singleFunctor_obj X 𝓕 h𝓕qc) hK)
    (@DerivedCategory.isZero_of_isLE _ _ _ _ _ a i hi hE)

end AlgebraicGeometry
