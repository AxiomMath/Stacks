module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SeparableExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilChernCharacter
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.Product

/-!
# Nonvanishing of the cohomology of the point and of `c₁^H(𝒪_{𝐏¹}(1))`

Let `k` be a field, `F` a field and `𝔇` data (D0), (D1), (D2') as in Section 45.14 of the Stacks
Project (`Stacks.WeilCohomology.FirstChernClassData`). This file records three elementary
consequences of the axioms that the proofs of Lemmas 0FVR, 0FVS and 0FIS of the source use
silently:

* by the Künneth axiom (A5), `H^*(Spec k) = F ≠ 0`;
* a Tate twist of a nonzero vector space is nonzero;
* by (A3) and (A5), the class `c = c₁^H(𝒪_P(1))` of the projective line `P = 𝐏(𝒪²) ⟶ Spec k` is
  nonzero: were it zero, the projective bundle formula would kill `(0, a)` for every
  `a ∈ H^*(Spec k)(-1)`.

The nonvanishing `H^*(Spec K) ≠ 0` for a finite separable extension `K/k`, from (A3), (A4) and
(A5), is the base's `Stacks.WeilCohomology.FirstChernClassData.nontrivial_H_spec`.

## Main results

* `Stacks.WeilDeRham.nontrivial_H_point`: `H^*(Spec k) ≠ 0`, from (A5).
* `Stacks.WeilDeRham.bundleClass_lineModule_ne_zero`: `c₁^H(𝒪_{𝐏¹}(1)) ≠ 0`, from (A3) and (A5).

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FVR](https://stacks.math.columbia.edu/tag/0FVR)
* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u w

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- By (A5), `H^*(Spec k) = F` is nonzero. -/
theorem nontrivial_H_point (hA5 : 𝔇.KunnethAxiom) : Nontrivial (𝔇.H (point k)) := by
  refine ⟨⟨0, 1, fun h => zero_ne_one (α := F) (hA5.1.1 ?_)⟩⟩
  simp only [Algebra.linearMap_apply, map_zero, map_one]
  exact h

/-- A Tate twist of a nonzero vector space is nonzero: the Tate line is one-dimensional. -/
theorem nontrivial_tateTwist (V : Type w) [AddCommGroup V] [Module F V] [Nontrivial V] (n : ℤ) :
    Nontrivial (tateTwist F 𝔇.tate V n) :=
  (tateTwistCoordinates (tateLineCoordinate 𝔇.finrank_tate) n).toEquiv.nontrivial

/-- **`c₁^H(𝒪_P(1)) ≠ 0` for the projective line `P = 𝐏(𝒪²)`** over the point, `𝒪²` being the
base's `Stacks.WeilCohomology.FirstChernClassData.pointFreeRankTwo`. Were it zero, the projective
bundle formula (A3) would send `(0, a)` to `0` for every `a ∈ H^*(Spec k)(-1)`, and that twist is
nonzero by (A5). -/
theorem bundleClass_lineModule_ne_zero (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom) :
    𝔇.bundleClass (point k) (FirstChernClassData.pointFreeRankTwo k) 1 ≠ 0 := by
  intro hc
  have := nontrivial_H_point 𝔇 hA5
  have := nontrivial_tateTwist 𝔇 (𝔇.H (point k)) (-(((1 : Fin (1 + 1)) : ℕ) : ℤ))
  obtain ⟨y, hy⟩ :=
    exists_ne (0 : tateTwist F 𝔇.tate (𝔇.H (point k)) (-(((1 : Fin (1 + 1)) : ℕ) : ℤ)))
  let a : ∀ i : Fin (1 + 1), tateTwist F 𝔇.tate (𝔇.H (point k)) (-((i : ℕ) : ℤ)) :=
    Pi.single 1 y
  have h0 : 𝔇.bundleFormula (point k) (FirstChernClassData.pointFreeRankTwo k) 1 a =
      𝔇.bundleFormula (point k) (FirstChernClassData.pointFreeRankTwo k) 1 0 := by
    simp [FirstChernClassData.bundleFormula, Fin.sum_univ_two, a, FirstChernClassData.twistPow, hc]
  exact hy (by simpa [a] using congrFun ((hA3 _ _ 1 inferInstance).1 h0) 1)

/-- Cup product with `1` on the left is the identity on twisted classes. -/
theorem tateCupLeft_cup_one (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (v : tateTwist F 𝔇.tate (𝔇.H X) n) :
    tateCupLeft (L := 𝔇.tate) (𝔇.cup X) n 1 v = v := by
  have h : (𝔇.cup X) 1 = LinearMap.id := LinearMap.ext fun x => one_mul x
  simp [tateCupLeft, tateTwistMap, h]

end Stacks.WeilDeRham

end
