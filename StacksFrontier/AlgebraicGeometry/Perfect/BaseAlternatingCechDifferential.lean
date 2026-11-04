module

public import StacksFrontier.AlgebraicGeometry.Perfect.BaseAlternatingCechBaseChangeDegreewise

/-!
# The differential of the `ℤ`-indexed Čech model in nonnegative degrees

`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplex f U hU F` is the
`ℤ`-indexed, `A`-linear alternating Čech complex of `F`, and
`baseAlternatingCechComplexXIso f U hU F m` identifies its term in degree `m ≥ 0` with the term of
the `ℕ`-indexed alternating Čech complex `Stacks.Cech.alternatingCechModuleComplex f U F`. This
file records that these identifications carry one differential to the other, so that cocycles and
coboundaries of the model in nonnegative degrees are those of the alternating Čech complex.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexXIso_inv_comp_d`
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.d_comp_baseAlternatingCechComplexXIso_hom`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- **The degree identifications of the Čech model commute with the differentials.** -/
theorem d_comp_baseAlternatingCechComplexXIso_hom (m : ℕ) :
    (baseAlternatingCechComplex f U hU F).d (m : ℤ) ((m + 1 : ℕ) : ℤ) ≫
        (baseAlternatingCechComplexXIso f U hU F (m + 1)).hom =
      (baseAlternatingCechComplexXIso f U hU F m).hom ≫
        (Stacks.Cech.alternatingCechModuleComplex f U F).d m (m + 1) := by
  set K := Stacks.Cech.alternatingCechModuleComplex f U F
  set E := baseAlternatingCechComplexIsoExtend f U hU F
  set ex₀ := K.extendXIso ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f m)
  set ex₁ := K.extendXIso ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f (m + 1))
  ext x
  have h : ∀ (n : ℕ) y, (K.extendXIso ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f n)).hom (E.hom.f (n : ℤ) y) =
      (baseAlternatingCechComplexXIso f U hU F n).hom y := fun n y =>
    congr($(baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f U hU F n) y)
  have hc : E.hom.f ((m + 1 : ℕ) : ℤ) ((baseAlternatingCechComplex f U hU F).d (m : ℤ)
      ((m + 1 : ℕ) : ℤ) x) =
      (K.extend ComplexShape.embeddingUpNat).d (m : ℤ) ((m + 1 : ℕ) : ℤ) (E.hom.f (m : ℤ) x) :=
    congr($(E.hom.comm (m : ℤ) ((m + 1 : ℕ) : ℤ)) x).symm
  have hd := congr($(HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
    (ComplexShape.embeddingUpNat_f m) (ComplexShape.embeddingUpNat_f (m + 1))) (E.hom.f (m : ℤ) x))
  change (baseAlternatingCechComplexXIso f U hU F (m + 1)).hom
      ((baseAlternatingCechComplex f U hU F).d (m : ℤ) ((m + 1 : ℕ) : ℤ) x) =
    K.d m (m + 1) ((baseAlternatingCechComplexXIso f U hU F m).hom x)
  rw [← h (m + 1), hc, hd, ← h m x]
  change ex₁.hom (ex₁.inv (K.d m (m + 1) (ex₀.hom (E.hom.f (m : ℤ) x)))) = _
  exact Iso.inv_hom_id_apply ex₁ _

/-- `d_comp_baseAlternatingCechComplexXIso_hom`, read through the inverse identifications. -/
theorem baseAlternatingCechComplexXIso_inv_comp_d (m : ℕ) :
    (baseAlternatingCechComplexXIso f U hU F m).inv ≫
        (baseAlternatingCechComplex f U hU F).d (m : ℤ) ((m + 1 : ℕ) : ℤ) =
      (Stacks.Cech.alternatingCechModuleComplex f U F).d m (m + 1) ≫
        (baseAlternatingCechComplexXIso f U hU F (m + 1)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← d_comp_baseAlternatingCechComplexXIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
