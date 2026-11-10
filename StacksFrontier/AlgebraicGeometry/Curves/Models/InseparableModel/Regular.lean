module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Charts
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# A regular model with an inseparable component: regularity, flatness and a section

The model `X` of `Stacks.Models.InseparableModel` is regular and flat over `R`, chart by chart,
and has a section `Spec R ⟶ X` through the chart `D₊(z₁₁)` at `s = T = 0`.

## Main results

* `Stacks.Models.InseparableModel.isRegular_XR`
* `Stacks.Models.InseparableModel.flat_X_to_R`
* `Stacks.Models.InseparableModel.modelSection_comp_X_to_R`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

/-- The basic open `D₊(z)` of a chart is an affine open of `X`. -/
theorem isAffineOpen_chart (c : Fin 3) :
    IsAffineOpen (Proj.basicOpen grading (zA (chartVar c))) :=
  Proj.isAffineOpen_basicOpen grading _ (zA_mem _) Nat.one_pos

/-- The ring of sections of `X` over the chart `D₊(z)` is the explicit ring of the chart. -/
def chartSectionsEquiv (c : Fin 3) :
    chartRing c ≃+* Γ(XR, Proj.basicOpen grading (zA (chartVar c))) :=
  (chartEquiv c).trans
    (Proj.basicOpenIsoAway grading (zA (chartVar c)) (zA_mem _)
      Nat.one_pos).commRingCatIsoToRingEquiv

/-- **The model is regular.** -/
theorem isRegular_XR : IsRegular XR := by
  intro x
  have hx : x ∈ (⊤ : XR.Opens) := trivial
  rw [← iSup_basicOpen_chartVar, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨⟨_, isAffineOpen_chart c⟩, hc, ?_⟩
  have := isRegularRing_chartRing c
  exact IsRegularRing.of_ringEquiv (chartSectionsEquiv c)

/-- The structure map of a chart is the structure map of its explicit ring, transported along
`chartEquiv`. -/
theorem awayBase_eq (c : Fin 3) :
    awayBase c = (chartEquiv c).toRingHom.comp (algebraMap R (chartRing c)) :=
  RingHom.ext fun r => (chartEquiv_algebraMap c r).symm

/-- **The model is flat over `R`.** -/
instance flat_X_to_R : Flat X_to_R := by
  let : IsZariskiLocalAtSource @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ iSup_basicOpen_chartVar fun c => ?_
  have hι : (Proj.basicOpen grading (zA (chartVar c))).ι =
      (Proj.basicOpenIsoSpec grading (zA (chartVar c)) (zA_mem _) Nat.one_pos).hom ≫ chartι c := by
    rw [chartι, ← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [hι, Category.assoc, chartι_comp_X_to_R]
  have : Flat (Spec.map (CommRingCat.ofHom (awayBase c))) := by
    rw [Flat.SpecMap_iff]
    change (awayBase c).Flat
    rw [awayBase_eq]
    exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (flat_chartRing c))
      (RingHom.Flat.of_bijective (chartEquiv c).bijective)
  infer_instance

/-- The point `s = T = 0` of the explicit ring of the chart `D₊(z₁₁)`: the ring map
`R[s][T] ⧸ ((1 - t s²) T - π s²) → R`, `s, T ↦ 0`. -/
def chartTwoEval : chartRing 2 →+* R :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (Polynomial.evalRingHom 0) 0) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    convert mul_zero _
    suffices Polynomial.eval 0 ((Polynomial.C (Polynomial.X : Polynomial R) ^ 2).coeff 0) = 0 by
      simp [chartEq, chartX, chartY, this]
    rw [← Polynomial.C_pow, Polynomial.coeff_C_zero]
    simp)

/-- The point `s = T = 0` is a section of the structure map: `chartTwoEval` is the identity on
`R`. -/
theorem chartTwoEval_algebraMap (r : R) : chartTwoEval (algebraMap R (chartRing 2) r) = r := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial (Polynomial R)) (chartRing 2)]
  simp [chartTwoEval, Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_apply]

/-- A section `Spec R ⟶ X` of the model: the point `s = T = 0` of the chart `D₊(z₁₁)`. -/
def modelSection : Spec (.of R) ⟶ XR :=
  Spec.map (CommRingCat.ofHom (chartTwoEval.comp (chartEquiv 2).symm.toRingHom)) ≫ chartι 2

/-- **`modelSection` is a section of the structure morphism `X ⟶ Spec R`.** -/
theorem modelSection_comp_X_to_R : modelSection ≫ X_to_R = 𝟙 _ := by
  rw [modelSection, Category.assoc, chartι_comp_X_to_R, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change chartTwoEval ((chartEquiv 2).symm (awayBase 2 r)) = r
  rw [← chartEquiv_algebraMap, RingEquiv.symm_apply_apply, chartTwoEval_algebraMap]

end Stacks.Models.InseparableModel
