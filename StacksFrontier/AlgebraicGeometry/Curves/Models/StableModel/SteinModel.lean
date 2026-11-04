module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreMaps
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage

/-!
# The Stein factorization of a morphism of a regular proper model

In the situation of [Stacks, Tag 0C61] let `φ : X ⟶ P` be a morphism over `Spec R` to a proper
locally Noetherian `R`-scheme `P`. Its Stein factorization `X ⟶ Y ⟶ P` ([Stacks, Tag 03H0]) has a
proper surjective first factor `c` with `𝒪_Y = c_*𝒪_X` and a finite second factor `π`. The scheme
`Y` is integral, being dominated by the integral scheme `X` with `𝒪_Y = c_*𝒪_X`, and it is flat
over the discrete valuation ring `R` since it dominates `Spec R`.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_steinFactorization_model`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The Stein factorization of a morphism of the model to a proper `R`-scheme.** -/
theorem exists_steinFactorization_model {P : Scheme.{u}} (q : P ⟶ Spec (.of S.R)) [IsProper q]
    [IsLocallyNoetherian P] (φ : S.X ⟶ P) (hφ : φ ≫ q = S.X_to_R) :
    ∃ (Y : Scheme.{u}) (c : S.X ⟶ Y) (π : Y ⟶ P), c ≫ π = φ ∧ IsProper c ∧ IsFinite π ∧
      Function.Surjective c ∧
      IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom) ∧ IsIntegral Y ∧
      Flat (π ≫ q) := by
  have : IsIntegral S.X := S.toRegularModelSituation.isIntegral_X
  have : IsProper (φ ≫ q) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp φ q
  have : Surjective S.X_to_R := ⟨S.surjective_X_to_R⟩
  have : Surjective (φ.toNormalization ≫ φ.fromNormalization ≫ q) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hφ]
    infer_instance
  have : Surjective (φ.fromNormalization ≫ q) := Surjective.of_comp φ.toNormalization _
  have hdom : IsDominant (φ.fromNormalization ≫ q) := inferInstance
  have hη : (φ.fromNormalization ≫ q) (genericPoint φ.normalization) =
      genericPoint (Spec (.of S.R)) :=
    ((tfae_isDominant_of_isIntegral (φ.fromNormalization ≫ q)).out 1 2).mp hdom
  exact ⟨φ.normalization, φ.toNormalization, φ.fromNormalization,
    Scheme.Hom.toNormalization_fromNormalization φ,
    Stacks.SteinFactorization.isProper_toNormalization φ,
    Stacks.SteinFactorization.isFinite_fromNormalization φ,
    (Stacks.SteinFactorization.surjective_toNormalization φ).surj,
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      φ.toNormalization).mp
      (Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper φ),
    inferInstance, flat_of_genericPoint_map_eq _ hη⟩

end Stacks.Models.RegularProperModelSituation

end
