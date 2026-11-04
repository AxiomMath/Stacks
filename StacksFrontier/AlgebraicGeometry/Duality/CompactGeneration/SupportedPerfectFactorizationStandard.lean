module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.RestrictAndPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.TensorSupport
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedPerfectFactorization
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportModelComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The supported-perfect factorization at the standard model

Let `X` be a quasi-compact quasi-separated scheme and `T ⊆ X` a closed subset with quasi-compact
complement. At the standard model `CategoryTheory.HasDerivedCategory.standard` of `D(𝒪_X)`, every
morphism `𝒪_X[0] ⟶ K` into a complex with quasi-coherent cohomology supported on `T` factors
through a perfect complex supported on `T`, and there is a perfect `I ⟶ 𝒪_X[0]`, an isomorphism
over `X ∖ T`, whose composite with `𝒪_X[0] ⟶ K` is zero.

## Main results

* `Stacks.Duality.Supported.exists_fac_isPerfect_cohomologySupportedOn`: the factorization at the
  standard model.
* `Stacks.Duality.Supported.isPerfect_structureSheaf_standard`: `𝒪_X[0]` is perfect at the
  standard model.
* `Stacks.Duality.Supported.exists_isPerfect_isIso_derivedRestrict_comp_eq_zero`: the
  conclusion of [Stacks, Tag 0A9C] for a map out of the structure sheaf, at the standard model.

## Implementation notes

The factorization is transported from the locally small model along the comparison
`StacksDraft.DerivedModel.modelEquiv` of the two models of the derived category, an equivalence
of categories; `StacksDraft.DerivedModel.modelSingleFunctorIso` identifies `𝒪_X[0]` at one model
with `𝒪_X[0]` at the other.

## References

* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.PerfectComplexes

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.Supported

variable {X : Scheme.{u}}

/-! ### The factorization at the standard model -/

/-- **The supported-perfect factorization at `CategoryTheory.HasDerivedCategory.standard`.** Let
`X` be a quasi-compact quasi-separated scheme and `T ⊆ X` closed with quasi-compact complement,
and let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology supported on `T`. Then every
morphism `𝒪_X[0] ⟶ K` factors through a perfect complex with cohomology supported on `T`. -/
theorem exists_fac_isPerfect_cohomologySupportedOn [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) (K : DerivedCategory X.Modules)
    (hKqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) K)
    (hKT : CohomologySupportedOn X.ringCatSheaf T K)
    (ζ : (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      K) :
    ∃ (Q : DerivedCategory X.Modules)
      (a : (DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶ Q) (b : Q ⟶ K),
      IsPerfect (X := X.toRingedSpace) Q ∧ CohomologySupportedOn X.ringCatSheaf T Q ∧
        a ≫ b = ζ := by
  obtain ⟨Q, a, b, hQp, hQs, hab⟩ :=
    exists_fac_perfectSupported hT hTc ((standardToLocallySmall X).functor.obj K)
      ((StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) _ _ K).2 hKqc)
      (fun i x hx ↦ (Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff
        X.ringCatSheaf (HasDerivedCategory.standard X.Modules) _ K i x).1 (hKT i x hx))
      ((standardToLocallySmallStructureSheafIso X).inv ≫ (standardToLocallySmall X).functor.map ζ)
  refine ⟨(standardToLocallySmall X).inverse.obj Q,
    (standardToLocallySmall X).functor.preimage
      ((standardToLocallySmallStructureSheafIso X).hom ≫ a ≫
        ((standardToLocallySmall X).counitIso.app Q).inv),
    (standardToLocallySmall X).functor.preimage
      (((standardToLocallySmall X).counitIso.app Q).hom ≫ b), ?_, ?_, ?_⟩
  · exact (Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff
      (HasDerivedCategory.standard X.Modules) _ _).2
      (isPerfect_of_iso_locallySmall X ((standardToLocallySmall X).counitIso.app Q).symm hQp)
  · exact fun i x hx ↦ (Stacks.DerivedQCoh.AnyModel.isZero_stalk_homology_modelEquiv_iff
      X.ringCatSheaf (HasDerivedCategory.standard X.Modules) _ _ i x).2
      (cohomologySupportedOn_of_iso_locallySmall X T
        ((standardToLocallySmall X).counitIso.app Q).symm hQs i x hx)
  · refine (standardToLocallySmall X).functor.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hab, Iso.hom_inv_id_assoc]

/-- **`𝒪_X[0]` is a perfect object of `D(𝒪_X)` at the standard model.** -/
theorem isPerfect_structureSheaf_standard (X : Scheme.{u}) :
    IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  (Stacks.DerivedQCoh.AnyModel.isPerfect_modelEquiv_iff
      (HasDerivedCategory.standard X.Modules) _ _).2
    (isPerfect_of_iso_locallySmall X (standardToLocallySmallStructureSheafIso X).symm
      (isPerfect_structureSheaf_locallySmall X))

/-! ### [Stacks, Tag 0A9C] for a map out of the structure sheaf -/

/-- **[Stacks, Tag 0A9C] for a map out of the structure sheaf.** Let `X` be a quasi-compact
quasi-separated scheme, let `T ⊆ X` be closed with quasi-compact complement, let `K` be an object
of `D(𝒪_X)` with quasi-coherent cohomology supported on `T` and let `ζ : 𝒪_X[0] ⟶ K`. Then there
are a perfect complex `I` and a map `f : I ⟶ 𝒪_X[0]` which restricts to an isomorphism over
`U = X ∖ T` and satisfies `f ≫ ζ = 0`. -/
theorem exists_isPerfect_isIso_derivedRestrict_comp_eq_zero [CompactSpace X]
    [QuasiSeparatedSpace X] {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (K : DerivedCategory X.Modules)
    (hKqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) K)
    (hKT : CohomologySupportedOn X.ringCatSheaf T K)
    (ζ : (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      K) :
    ∃ (I : DerivedCategory X.Modules) (f : I ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)),
      IsPerfect (X := X.toRingedSpace) I ∧
        IsIso ((Scheme.Modules.restrictFunctor
          (complementOpenOfIsClosed hT).ι).mapDerivedCategory.map f) ∧ f ≫ ζ = 0 := by
  obtain ⟨Q, a, b, hQp, hQs, hab⟩ :=
    exists_fac_isPerfect_cohomologySupportedOn hT hTc K hKqc hKT ζ
  obtain ⟨I, f, g, hTri⟩ := distinguished_cocone_triangle₁ a
  refine ⟨I, f, ?_, ?_, ?_⟩
  · exact @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
      X.toRingedSpace (HasDerivedCategory.standard X.Modules) _ hTri
      (isPerfect_structureSheaf_standard X) hQp
  · exact (Triangle.isZero₃_iff_isIso₁ _ ((Scheme.Modules.restrictFunctor
      (complementOpenOfIsClosed hT).ι).mapDerivedCategory.map_distinguished _ hTri)).1
      (Stacks.DerivedQCoh.isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl T _
        subset_rfl Q hQs)
  · rw [← hab, ← Category.assoc, show f ≫ a = 0 from comp_distTriang_mor_zero₁₂ _ hTri,
      zero_comp]

end Stacks.Duality.Supported

end
