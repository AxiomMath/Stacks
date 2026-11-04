module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory

/-!
# Complements to the cycle class map of Tag 0FIF

Let `k` be a field, `F` a field of characteristic zero, and let data (D0), (D1), (D2') satisfy
the conditions (A1) – (A4) of Section 45.14 of the Stacks Project. Lemma 0FIF gives the cycle
class map `γ` for the cohomological Chern character `ch^H` of Tag 0FIE, a rule `ch` with
`h : 𝔇.IsCohomologicalChernCharacter ch`: on `CH^*(X) ⊗ 𝐐` (`h.cycleClassMap`), on `CH^i(X)`
with values in `H^*(X)(i)` (`h.codimensionCycleClass`) and on `CH^i(X)` with values in
`H^{2i}(X)(i)` (`h.cycleClassGrade`), in the namespace
`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`. This file records three
consequences of the construction used by the Weil cohomology chapter which are not stated in that
form there:

* the coefficient of `tⁿ` of `ch^H(α')` vanishes for `n ≠ i` when `ψ²(α') = 2^i α'` (Lemma 0FIA,
  as used in the proof of Lemma 0FIF);
* `γ(ch(α') ∩ [X])` vanishes in degree `n ≠ i` when the components `ch_p(α') ∩ [X]`, `p ≠ i`,
  vanish;
* the graded form of axiom (C)(a): `γ(f^!β) = f^*γ(β)` in `H^{2i}(X)(i)`.

## Main results

* `Stacks.WeilDeRham.coeff_rationalCohomologicalChernCharacter_eq_zero_of_rationalSecondAdams`
* `Stacks.WeilDeRham.cycleClass_codimensionGysin`

## References

* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Section 0FEX](https://stacks.math.columbia.edu/tag/0FEX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open Stacks.Chow Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u w

namespace Stacks.WeilDeRham

open FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom)

include hA1 hA3 in
/-- **The coefficients of `ch^H(α')` for an eigenvector of `ψ²`**: if `ψ²(α') = 2^i α'` for
`α' ∈ K₀(Vect(X)) ⊗ 𝐐`, then the coefficient of `tⁿ` of `ch^H(α')` vanishes for `n ≠ i`, since
`ch^H_n(ψ²(α')) = 2^n ch^H_n(α')` (Lemma 0FIA). -/
theorem coeff_rationalCohomologicalChernCharacter_eq_zero_of_rationalSecondAdams
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    {a : ℚ ⊗[ℤ] VectorBundleKZero ((toScheme k).obj X)} {i : ℕ}
    (ha : rationalSecondAdams ((toScheme k).obj X) a = (2 ^ i : ℚ) • a) {n : ℕ} (hn : n ≠ i) :
    PowerSeries.coeff n (h.rationalLift X a) = 0 := by
  have key := h.coeff_rationalLift_rationalSecondAdams hA1 hA3 X a n
  rw [ha, map_smul, PowerSeries.coeff_smul, ← Nat.cast_smul_eq_nsmul ℚ] at key
  have h2 : ((2 : ℚ) ^ i - 2 ^ n) • PowerSeries.coeff n (h.rationalLift X a) = 0 := by
    rw [sub_smul, key]; push_cast; exact sub_self _
  have hne : ((2 : ℚ) ^ i - 2 ^ n) ≠ 0 := by
    intro h'
    rw [sub_eq_zero] at h'
    exact hn (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h'.symm))
  rw [← one_smul ℚ (PowerSeries.coeff n _), ← inv_mul_cancel₀ hne, mul_smul, h2, smul_zero]

/-- **The graded form of axiom (C)(a) for the cycle class map of Tag 0FIF**: `γ(f^!β) = f^*γ(β)`
in `H^{2i}(X)(i)` for a morphism `f : X ⟶ Y` of smooth projective schemes over `k` and
`β ∈ CH^i(Y)`, `f^!` being the Gysin map of Stacks 0FF3 graded by codimension. -/
theorem cycleClass_codimensionGysin {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (i : ℕ) (β : codimensionChowGroup k Y.obj.hom i) :
    h.cycleClassGrade hA1 hA3 X i (codimensionGysin X.obj.hom Y.obj.hom (w f) i β) =
      tateTwistMap (gradedPieceMap (𝔇.grade Y) (𝔇.grade X) (𝔇.pull f) (𝔇.pull_grade f) _) _
        (h.cycleClassGrade hA1 hA3 Y i β) := by
  refine (tateTwistCoordinates 𝔇.coord (i : ℤ)).injective (Subtype.ext ?_)
  rw [tateTwistCoordinates_map]
  show _ = 𝔇.pull f ((tateTwistCoordinates 𝔇.coord (i : ℤ)
    (h.cycleClassGrade hA1 hA3 Y i β) : 𝔇.grade Y (2 * (i : ℤ))) : 𝔇.H Y)
  simp only [IsCohomologicalChernCharacter.cycleClassGrade, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearEquiv.apply_symm_apply]
  rw [h.codimensionCycleClass_codimensionGysin, κ_pullTw]

end Stacks.WeilDeRham

end
