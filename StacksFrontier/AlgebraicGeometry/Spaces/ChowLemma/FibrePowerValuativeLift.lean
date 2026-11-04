module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projections of a finite fibre power, and the valuative lift through them

Each projection `Stacks.Chow.overProdπ` of a finite fibre product `Stacks.Chow.overProd` over a
base of proper morphisms is proper, and a valuative square over a proper or H-projective
morphism of schemes has a lift.

## Main results

* `AlgebraicGeometry.isProper_overProdπ`: each projection of a finite fibre product over a base
  of proper morphisms is proper.
* `AlgebraicGeometry.exists_valuativeLift_of_isProper`: a valuative square over a proper
  morphism of schemes has a lift.
* `AlgebraicGeometry.exists_valuativeLift_of_isProjectiveMorphism`: the same for an H-projective
  morphism.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 01KF](https://stacks.math.columbia.edu/tag/01KF)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Each projection of a finite fibre product over a base of proper morphisms is proper. -/
theorem isProper_overProdπ {S : Scheme.{u}} {n : ℕ} {Y : Fin n → Scheme.{u}}
    (g : ∀ i, Y i ⟶ S) [∀ i, IsProper (g i)] (i : Fin n) :
    IsProper (Stacks.Chow.overProdπ g i) := by
  have hcomp : IsProper (Stacks.Chow.overProdπ g i ≫ g i) := by
    rw [Stacks.Chow.overProdπ_comp]
    infer_instance
  have := hcomp
  exact IsProper.of_comp (Stacks.Chow.overProdπ g i) (g i)

/-- A valuative square over a proper morphism of schemes has a lift. Let `R` be a valuation ring
with fraction field `K`, and let a point `Spec K ⟶ X` and a point `Spec R ⟶ S` agree in `S`. If
`f : X ⟶ S` is proper then the first point extends to `Spec R ⟶ X` over `S`. -/
@[sga "7 X 1.12" "Direction"]
theorem exists_valuativeLift_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X) (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (hcomm : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) :
    ∃ l : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ f = i₂ := by
  have hcl : UniversallyClosed f := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hcl
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ :=
    (hcl.1 { R := R, K := K, i₁ := i₁, i₂ := i₂, commSq := ⟨hcomm⟩ }).exists_lift
  exact ⟨l, hl₁, hl₂⟩

/-- A valuative square over an H-projective morphism of schemes has a lift. -/
theorem exists_valuativeLift_of_isProjectiveMorphism {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsProjectiveMorphism f)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (CommRingCat.of K) ⟶ X) (i₂ : Spec (CommRingCat.of R) ⟶ S)
    (hcomm : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) :
    ∃ l : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ f = i₂ :=
  have := isProper_of_isProjectiveMorphism f hf
  exists_valuativeLift_of_isProper f R K i₁ i₂ hcomm

end AlgebraicGeometry

end
