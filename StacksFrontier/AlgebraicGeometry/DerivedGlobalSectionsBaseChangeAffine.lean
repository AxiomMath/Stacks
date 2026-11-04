module

public import StacksFrontier.AlgebraicGeometry.AffineDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLerayOverRingMap
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardQuasiCoherence
public import StacksFrontier.CategoryTheory.Adjunction.MatePointwiseIsIso
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent

/-!
# Derived global sections commute with base change over an affine base, on `Spec A`

Let `φ : A ⟶ B` be a map of commutative rings and `b : Spec B ⟶ Spec A` the induced morphism.
For `G ∈ D_QCoh(𝒪_{Spec A})` the pullback map
`θ : RΓ(Spec A, G) ⟶ RΓ(Spec B, Lb^* G)` of `AlgebraicGeometry.LerayOver.pullbackSectionsMap`
has an adjoint `RΓ(Spec A, G) ⊗ᴸ_A B ⟶ RΓ(Spec B, Lb^* G)`, and this adjoint is an isomorphism.

## Main results

* `AlgebraicGeometry.LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap_spec` — the
  statement above.

## Implementation notes

The derived categories are taken at the standard model.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPullback derivedAdjunction)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.LerayOver

variable (R : CommRingCat.{u})

/-- The quasi-coherence of the cohomology sheaves of an object of `D(𝒪_X)`. -/
abbrev IsQuasicoherentDerived {X : Scheme.{u}}
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) : Prop :=
  ∀ i : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent

/-- Derived global sections on `Spec R` are bijective on morphisms between objects of
`D_QCoh(𝒪_{Spec R})`. -/
theorem bijective_sections_map_spec {E E' : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace))}
    (hE : IsQuasicoherentDerived E) :
    Function.Bijective (fun χ : E ⟶ E' => (sections (𝟙 (Spec R))).map χ) := by
  have : IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app E) :=
    StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_counit_app R ⟨E, hE⟩
  exact Adjunction.bijective_map_of_isIso_counit_app
    (derivedTildeGlobalSectionsAdjunction R).val E E'

/-- Every object of `D(R)` is derived global sections of an object of `D_QCoh(𝒪_{Spec R})`. -/
theorem exists_sections_spec_iso (N : DerivedCategory (ModuleCat.{u} R)) :
    ∃ N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)),
      IsQuasicoherentDerived N' ∧ Nonempty ((sections (𝟙 (Spec R))).obj N' ≅ N) := by
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit R
  exact ⟨((derivedTilde R).obj N).obj, ((derivedTilde R).obj N).property,
    ⟨(asIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app N)).symm⟩⟩

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The square formed by `Spec B ⟶ Spec A` and the identities of the two spectra commutes. -/
theorem specMap_comp_id :
    Spec.map (CommRingCat.ofHom φ) ≫ 𝟙 (Spec (CommRingCat.of A)) =
      𝟙 (Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp

/-- **Derived global sections commute with base change on an affine scheme.** For
`G ∈ D_QCoh(𝒪_{Spec A})` the adjoint `RΓ(Spec A, G) ⊗ᴸ_A B ⟶ RΓ(Spec B, Lb^* G)` of the pullback
map along `b = Spec φ` is an isomorphism. -/
theorem isIso_derivedBaseChangeComparison_pullbackSectionsMap_spec
    (G : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (Spec (CommRingCat.of A)).toRingedSpace)))
    (hG : IsQuasicoherentDerived G) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      (pullbackSectionsMap φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)
        G)) := by
  let b := (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, u, u} φ
  have hD : D.functor.IsLeftDerivedFunctor D.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  let adj' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    A B _ _ φ _ _ D.functor D.comparison hD
  exact Adjunction.isIso_homEquiv_symm_map_unit_comp_of_bijective (derivedAdjunction b) adj'
    (sections (𝟙 _)) (sections (𝟙 _))
    (lerayIso φ (𝟙 _) (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) (specMap_comp_id φ)).inv G
    IsQuasicoherentDerived (exists_sections_spec_iso (CommRingCat.of B))
    (fun N' hN' => bijective_sections_map_spec (CommRingCat.of B)
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ G hG))
    (fun N' hN' => bijective_sections_map_spec (CommRingCat.of A) hG)

end AlgebraicGeometry.LerayOver
