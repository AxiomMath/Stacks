module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.AffineSupportedLift
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback

/-!
# Extending `F ⊕ F[1]` together with a map, from a quasi-compact open of an affine scheme

Let `X` be an affine scheme, `T ⊆ X` a closed subset with `X ∖ T` quasi-compact, `U ⊆ X` a
quasi-compact open with inclusion `ι : U ⟶ X`, and let `F` be a perfect object of `D(𝒪_U)`
supported on `T ∩ U`.  For an object `G` of `D_QCoh(𝒪_X)` and a morphism
`α : F ⟶ ι^*G` there are a perfect object `Q` of `D(𝒪_X)` supported on `T`, an
isomorphism `c : F ⊕ F[1] ≅ ι^*Q` and a morphism `b : Q ⟶ G` with `ι^*b ∘ c = α ∘ pr₁`.

Here `ι^*` is restriction along `ι`, the functor `Stacks.Duality.OpenImmersion.derivedRestrict`.

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_supported_lift_biprod_shift_hom_of_isAffine`: the lift of
  `α ∘ pr₁` described above.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace CategoryTheory.MonoidalCategory

universe u

namespace Stacks.DerivedQCoh.OpenLift

open Stacks.Cohomology.SiteModules Stacks.Cohomology.PerfectComplexes
open _root_.Stacks.StrictlyPerfect Stacks.DerivedQCoh
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- In any category, if `m ≫ (eR⁻¹ ≫ e⁻¹ ≫ α) = g` for an isomorphism `m`, then
`(e ≪≫ eR ≪≫ m⁻¹) ≫ g = α`. -/
theorem iso_trans_trans_symm_comp_eq {C : Type*} [Category C] {A B C' D Y : C} (e : A ≅ B)
    (eR : B ≅ C') (m : D ⟶ C') [IsIso m] (g : D ⟶ Y) (α : A ⟶ Y)
    (h : m ≫ eR.inv ≫ e.inv ≫ α = g) :
    (e ≪≫ eR ≪≫ (asIso m).symm).hom ≫ g = α := by
  simp [← h]

/-- Let `X` be an affine scheme, `T ⊆ X` closed with `X ∖ T` quasi-compact, `U ⊆ X` a
quasi-compact open, `F` a perfect object of `D(𝒪_U)` supported on `T ∩ U`, `G` an object of
`D(𝒪_X)` with quasi-coherent cohomology and `α : F ⟶ ι^*G`. Then there are a perfect `Q`
supported on `T`, an isomorphism `c : F ⊕ F[1] ≅ ι^*Q` and `b : Q ⟶ G` with
`c ≫ ι^*b = pr₁ ≫ α`. -/
theorem exists_supported_lift_biprod_shift_hom_of_isAffine
    (X : Scheme.{u}) [IsAffine X] (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F)
    (hFT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) F)
    (G : DerivedCategory (SheafOfModules X.ringCatSheaf))
    (hG : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj G).IsQuasicoherent)
    (α : F ⟶ (derivedRestrict U.ι).obj G) :
    ∃ Q : DerivedCategory (SheafOfModules X.ringCatSheaf),
      IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) Q ∧ CohomologySupportedOn X.ringCatSheaf T Q ∧
        ∃ (c : F ⊞ F⟦(1 : ℤ)⟧ ≅ (derivedRestrict U.ι).obj Q) (b : Q ⟶ G),
          c.hom ≫ (derivedRestrict U.ι).map b = biprod.fst ≫ α := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf
  obtain ⟨P, hP, hPT, ⟨e⟩⟩ :=
    exists_isPerfectComplex_supported_restrict_iso_biprod_shift_of_isAffine X T hT hTc U hU F hF hFT
  let E : DerivedCategory (SheafOfModules X.ringCatSheaf) := DerivedCategory.Q.obj P
  have hE : IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E := ⟨P, hP, ⟨Iso.refl E⟩⟩
  let R := derivedRestrict U.ι
  let eRM := AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U
  let eR : DerivedCategory.Q.obj
      (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
        U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ R.obj E :=
    (AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X.toRingedSpace U P).symm ≪≫
      eRM.app E
  let α' : R.obj E ⟶ R.obj G := eR.inv ≫ e.inv ≫ biprod.fst ≫ α
  obtain ⟨I, b, γ, -, -, hEI, hiso, hcomm⟩ :=
    exists_isPerfect_derivedTensor_lift_of_isAffine X U hU E G hE hG α'
  refine ⟨E ⊗ I, hEI,
    Stacks.SheafOfModules.cohomologySupportedOn_derivedTensor_left X.sheaf T E I hPT, ?_⟩
  have := hiso
  exact ⟨_, γ, iso_trans_trans_symm_comp_eq e eR _ _ (biprod.fst ≫ α) hcomm⟩

/-- Restriction to an open preserves quasi-coherence of the cohomology. -/
theorem isQuasicoherent_homology_derivedRestrict {X : Scheme.{u}} (U : X.Opens)
    (G : DerivedCategory X.Modules)
    (hG : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj G).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
      ((derivedRestrict U.ι).obj G)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι).app G).symm)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel U.ι G hG i)

end Stacks.DerivedQCoh.OpenLift
