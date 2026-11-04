module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueConstants

/-!
# The norm map of a simple extension `k ⊂ k[X] ⧸ φ`

Let `k` be a field and `φ ∈ k[X]` monic irreducible of degree `d`, with residue field
`κ = k[X] ⧸ φ`. Following Milnor and Bass–Tate, the **norm map**

`N_φ : K^M_*(κ) ⟶ K^M_*(k)`, `N_φ(α) = -∂_∞(y)`,

where `y ∈ K^M_*(RatFunc k)` is any class whose residue at `φ` is `α` and whose residue at every
other closed point of `A¹_k` vanishes (`Stacks.Chow.simpleMilnorNorm`). Such a `y` exists by the
surjectivity half of Milnor's exact sequence (`Stacks.Chow.exists_isSingleResidueLift_ring`), and
`∂_∞(y)` does not depend on it, because two choices differ by a class killed by every residue,
hence by a class of `K^M_*(k)` (`Stacks.Chow.infinityResidueRing_eq_of_isSingleResidueLift`).

## Properties

* `N_φ` preserves the degree (`Stacks.Chow.simpleMilnorNorm_mem_milnorKGrading`): a homogeneous
  `α` has a homogeneous lift.
* **Degree zero:** `N_φ(1) = d = [κ : k]` (`Stacks.Chow.simpleMilnorNorm_one`). The lift of `1` is
  `{φ}`, and `φ(1/X) = X^{-d} φ^{rev}(X)` with `φ^{rev}(0) = 1`, so `∂_∞ {φ} = -d`.
* **Projection formulas:** `N_φ(ι(z) α) = z N_φ(α)` and `N_φ(α ι(z)) = N_φ(α) z` for
  `z ∈ K^M_*(k)` (`Stacks.Chow.simpleMilnorNorm_map_mul`, `Stacks.Chow.simpleMilnorNorm_mul_map`),
  from the linearity of the residues over the constants
  (`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueConstants`).

## Main definitions

* `Stacks.Chow.simpleMilnorNorm` — the norm `N_φ` on the whole Milnor K-ring.

## Main results

* `Stacks.Chow.simpleMilnorNorm_eq` — `N_φ(α) = -∂_∞(y)` for every lift with a single residue.
* `Stacks.Chow.simpleMilnorNorm_mem_milnorKGrading`, `Stacks.Chow.simpleMilnorNorm_one`,
  `Stacks.Chow.simpleMilnorNorm_map_mul`, `Stacks.Chow.simpleMilnorNorm_mul_map`.
* `Stacks.Chow.infinityResidueRing_milnorKSymbol_monic` — `∂_∞ {φ} = -deg φ`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §2.
* H. Bass, J. Tate, *The Milnor ring of a global field*, LNM 342 (1973), §I.5.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable {k : Type u} [Field k]

attribute [local instance] Ideal.Quotient.field
attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial

/-! ### The residue at infinity of a monic polynomial -/

/-- A ring homomorphism out of `k[X]` evaluates a polynomial at the image of `X`. -/
private theorem ringHom_polynomial_apply_eq_eval₂ {R : Type*} [CommRing R]
    (g : Polynomial k →+* R) (f : Polynomial k) : g f = f.eval₂ (g.comp C) (g X) := by
  simpa only [eval₂_C_X] using Polynomial.hom_eval₂ f C g X

/-- The involution `X ↦ 1/X` evaluates a polynomial at `1/X`. -/
theorem projectiveLineChartInversion_algebraMap_eq_eval₂ (f : Polynomial k) :
    AlgebraicGeometry.projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) f) =
      f.eval₂ (constantsHom k) (algebraMap (Polynomial k) (RatFunc k) X)⁻¹ := by
  refine (ringHom_polynomial_apply_eq_eval₂
    ((AlgebraicGeometry.projectiveLineChartInversion k).toRingHom.comp
      (algebraMap (Polynomial k) (RatFunc k))) f).trans ?_
  congr 1
  · exact RingHom.ext fun c ↦ projectiveLineChartInversion_constantsHom c
  · exact AlgebraicGeometry.projectiveLineChartInversion_X k

/-- Evaluating at `X` through the constants is the inclusion of the polynomials. -/
theorem eval₂_constantsHom_X (f : Polynomial k) :
    f.eval₂ (constantsHom k) (algebraMap (Polynomial k) (RatFunc k) X) =
      algebraMap (Polynomial k) (RatFunc k) f :=
  (ringHom_polynomial_apply_eq_eval₂ (algebraMap (Polynomial k) (RatFunc k)) f).symm

/-- **`f(1/X) = f^{rev}(X) · X^{-deg f}`.** -/
theorem projectiveLineChartInversion_algebraMap (f : Polynomial k) :
    AlgebraicGeometry.projectiveLineChartInversion k (algebraMap (Polynomial k) (RatFunc k) f) =
      algebraMap (Polynomial k) (RatFunc k) f.reverse *
        ((algebraMap (Polynomial k) (RatFunc k) X)⁻¹) ^ f.natDegree := by
  have hX : (algebraMap (Polynomial k) (RatFunc k) X)⁻¹ ≠ 0 :=
    inv_ne_zero (algebraMap_polynomial_ratFunc_ne_zero X_ne_zero)
  let := invertibleOfNonzero hX
  rw [projectiveLineChartInversion_algebraMap_eq_eval₂,
    ← eval₂_reverse_mul_pow (constantsHom k) (algebraMap (Polynomial k) (RatFunc k) X)⁻¹ f,
    invOf_eq_inv, inv_inv, eval₂_constantsHom_X]

/-- **At infinity, a monic polynomial `φ` is a unit times the `-deg φ`-th power of the
uniformizer, with unit part `1`:** the tame-symbol homomorphism at the origin sends the symbol of
`φ(1/X)` to `-deg φ · ξ`. -/
theorem dvrMilnorShiftMap_inversion_monic {φ : Polynomial k} (hφ : φ.Monic) :
    dvrMilnorShiftMap (F := RatFunc k) (irreducible_algebraMap_X (k := k))
        (milnorKRingMap (AlgebraicGeometry.projectiveLineChartInversion k).toRingHom
          (milnorKSymbol (RatFunc k) (polyUnit hφ.ne_zero))) =
      MilnorKShift.mk 0 ((-(φ.natDegree : ℤ)) • (1 : MilnorKRing _)) := by
  have hrev : φ.reverse ∉ (Ideal.span {(X : Polynomial k)}) := fun hmem ↦ by
    have h0 := X_dvd_iff.mp (Ideal.mem_span_singleton.mp hmem)
    rw [coeff_zero_reverse, hφ.leadingCoeff] at h0
    exact one_ne_zero h0
  obtain ⟨w, hw⟩ := IsLocalization.map_units (M := (Ideal.span {(X : Polynomial k)}).primeCompl)
    (localRingAtOrigin k) ⟨φ.reverse, Ideal.mem_primeCompl_iff.mpr hrev⟩
  have hx : ((Units.map ((AlgebraicGeometry.projectiveLineChartInversion k).toRingHom :
        RatFunc k →* RatFunc k) (polyUnit hφ.ne_zero) : (RatFunc k)ˣ) : RatFunc k) =
      algebraMap (localRingAtOrigin k) (RatFunc k) (w : localRingAtOrigin k) *
        (algebraMap (localRingAtOrigin k) (RatFunc k)
          (algebraMap (Polynomial k) (localRingAtOrigin k) X)) ^ (-(φ.natDegree : ℤ)) := by
    change AlgebraicGeometry.projectiveLineChartInversion k
      (algebraMap (Polynomial k) (RatFunc k) φ) = _
    rw [hw, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      projectiveLineChartInversion_algebraMap, zpow_neg, zpow_natCast, inv_pow]
  have hres : Units.map (residue (localRingAtOrigin k)).toMonoidHom w = 1 := by
    refine Units.ext ?_
    change residue (localRingAtOrigin k) (w : localRingAtOrigin k) = 1
    rw [hw]
    change residue (localRingAtOrigin k)
      (algebraMap (Polynomial k) (localRingAtOrigin k) φ.reverse) = 1
    rw [residue_algebraMap_polynomial, coeff_zero_reverse, hφ.leadingCoeff, map_one]
  rw [milnorKRingMap_milnorKSymbol, dvrMilnorShiftMap_milnorKSymbol]
  refine MilnorKShift.ext ?_ ?_
  · rw [main_dvrMilnorThetaHom, dvrFracUnitPart_eq_of_eq _ hx, hres, milnorKSymbol_one]
    rfl
  · rw [shift_dvrMilnorThetaHom, dvrFracOrd_eq_of_eq _ hx]
    rfl

/-- **`∂_∞ {φ} = -deg φ` for a monic polynomial `φ`.** -/
theorem infinityResidueRing_milnorKSymbol_monic {φ : Polynomial k} (hφ : φ.Monic) :
    infinityResidueRing k (milnorKSymbol (RatFunc k) (polyUnit hφ.ne_zero)) =
      (-(φ.natDegree : ℤ)) • (1 : MilnorKRing k) := by
  rw [infinityResidueRing_apply, dvrMilnorShiftMap_inversion_monic hφ, MilnorKShift.shift_mk,
    map_zsmul, map_one]

/-! ### The definition -/

/-- Every class of `K^M_*(k[X] ⧸ φ)` has a lift with a single residue. -/
theorem exists_isSingleResidueLift_ring' {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) :
    ∃ y : MilnorKRing (RatFunc k), IsSingleResidueLift φ α y := by
  rcases d with _ | e
  · exact (MonicIrreducibleOfDegree.isEmpty_zero.false φ).elim
  · exact exists_isSingleResidueLift_ring φ α

/-- A homogeneous class of `K^M_*(k[X] ⧸ φ)` has a homogeneous lift with a single residue. -/
theorem exists_isSingleResidueLift' {d : ℕ} (φ : MonicIrreducibleOfDegree k d) {i : ℕ}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) i) :
    ∃ y ∈ milnorKGrading (RatFunc k) (i + 1), IsSingleResidueLift φ α y := by
  rcases d with _ | e
  · exact (MonicIrreducibleOfDegree.isEmpty_zero.false φ).elim
  · exact exists_isSingleResidueLift φ hα

/-- The class `0` is a lift of `0` with a single residue. -/
theorem isSingleResidueLift_zero {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    IsSingleResidueLift φ 0 0 :=
  ⟨map_zero _, fun _ _ _ ↦ map_zero _⟩

/-- If `y` and `z` are lifts of `α` and `β` with a single residue, then `y + z` is a lift of
`α + β` with a single residue. -/
theorem IsSingleResidueLift.add {d : ℕ} {φ : MonicIrreducibleOfDegree k d}
    {α β : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})} {y z : MilnorKRing (RatFunc k)}
    (hy : IsSingleResidueLift φ α y) (hz : IsSingleResidueLift φ β z) :
    IsSingleResidueLift φ (α + β) (y + z) :=
  ⟨by rw [map_add, hy.1, hz.1], fun d' ψ hne ↦ by rw [map_add, hy.2 d' ψ hne, hz.2 d' ψ hne,
    add_zero]⟩

/-- **The norm map `N_φ : K^M_*(k[X] ⧸ φ) ⟶ K^M_*(k)` of a simple extension**: `N_φ(α) = -∂_∞(y)`
for a lift `y` of `α` with a single residue. -/
def simpleMilnorNorm {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ}) →+ MilnorKRing k where
  toFun α := -infinityResidueRing k (exists_isSingleResidueLift_ring' φ α).choose
  map_zero' := by
    rw [infinityResidueRing_eq_of_isSingleResidueLift
      (exists_isSingleResidueLift_ring' φ 0).choose_spec (isSingleResidueLift_zero φ), map_zero,
      neg_zero]
  map_add' α β := by
    rw [infinityResidueRing_eq_of_isSingleResidueLift
      (exists_isSingleResidueLift_ring' φ (α + β)).choose_spec
      ((exists_isSingleResidueLift_ring' φ α).choose_spec.add
        (exists_isSingleResidueLift_ring' φ β).choose_spec), map_add, neg_add]

/-- **`N_φ(α) = -∂_∞(y)` for every lift `y` of `α` with a single residue.** -/
theorem simpleMilnorNorm_eq {d : ℕ} {φ : MonicIrreducibleOfDegree k d}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})} {y : MilnorKRing (RatFunc k)}
    (hy : IsSingleResidueLift φ α y) : simpleMilnorNorm φ α = -infinityResidueRing k y := by
  change -infinityResidueRing k (exists_isSingleResidueLift_ring' φ α).choose = _
  rw [infinityResidueRing_eq_of_isSingleResidueLift
    (exists_isSingleResidueLift_ring' φ α).choose_spec hy]

/-- **`N_φ` preserves the degree.** -/
theorem simpleMilnorNorm_mem_milnorKGrading {d : ℕ} (φ : MonicIrreducibleOfDegree k d) {i : ℕ}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) i) :
    simpleMilnorNorm φ α ∈ milnorKGrading k i := by
  obtain ⟨y, hyi, hy⟩ := exists_isSingleResidueLift' φ hα
  rw [simpleMilnorNorm_eq hy]
  exact neg_mem (infinityResidueRing_mem_milnorKGrading hyi)

/-! ### Degree zero -/

/-- **`{φ}` is a lift of `1` with a single residue.** -/
theorem isSingleResidueLift_one {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    IsSingleResidueLift φ 1 (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) := by
  refine ⟨?_, fun d' ψ hne ↦ ?_⟩
  · have h := monicIrreducibleResidue_unitSymbolProd_mul_uniformizer φ []
    rwa [dvrFracUniformizer_irreducible_algebraMap_self (ne_zero φ), List.map_nil,
      milnorKSymbolProd_nil, show unitSymbolProd (RatFunc k)
        ([] : List (Localization.AtPrime (Ideal.span {poly φ}))ˣ) = 1 from rfl, one_mul] at h
  · refine monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ ?_
    rw [← milnorKSymbolProd_singleton]
    refine milnorKSymbolProd_mem_milnorKNotDvdFiltration fun v hv ↦ ?_
    rw [List.mem_singleton.mp hv]
    refine ⟨poly φ, ne_zero φ, fun hdvd ↦ hne ?_, rfl⟩
    exact Polynomial.eq_of_monic_of_associated (monic ψ) (monic φ)
      ((irreducible ψ).associated_of_dvd (irreducible φ) hdvd)

/-- **Degree zero: `N_φ(1) = deg φ = [k[X] ⧸ φ : k]`.** -/
theorem simpleMilnorNorm_one {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    simpleMilnorNorm φ 1 = (d : ℤ) • (1 : MilnorKRing k) := by
  rw [simpleMilnorNorm_eq (isSingleResidueLift_one φ),
    infinityResidueRing_milnorKSymbol_monic (monic φ), natDegree_eq φ, neg_smul, neg_neg]

/-! ### The projection formulas -/

/-- **`N_φ(ι(z) α) = z N_φ(α)`** for `z ∈ K^M_*(k)`. -/
theorem simpleMilnorNorm_map_mul {d : ℕ} (φ : MonicIrreducibleOfDegree k d) (z : MilnorKRing k)
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) :
    simpleMilnorNorm φ (milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly φ})) z * α) =
      z * simpleMilnorNorm φ α := by
  obtain ⟨y, hy⟩ := exists_isSingleResidueLift_ring' φ α
  have hzy : IsSingleResidueLift φ
      (milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly φ})) z * α)
      (milnorKRingMap (constantsHom k) z * y) :=
    ⟨by rw [monicIrreducibleResidue_constants_mul, hy.1], fun d' ψ hne ↦ by
      rw [monicIrreducibleResidue_constants_mul, hy.2 d' ψ hne, mul_zero]⟩
  rw [simpleMilnorNorm_eq hzy, simpleMilnorNorm_eq hy, infinityResidueRing_constants_mul, mul_neg]

/-- **`N_φ(α ι(z)) = N_φ(α) z`** for `z ∈ K^M_*(k)`. -/
theorem simpleMilnorNorm_mul_map {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) (z : MilnorKRing k) :
    simpleMilnorNorm φ (α * milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly φ})) z) =
      simpleMilnorNorm φ α * z := by
  obtain ⟨y, hy⟩ := exists_isSingleResidueLift_ring' φ α
  have hyz : IsSingleResidueLift φ
      (α * milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly φ})) z)
      (y * milnorKRingMap (constantsHom k) (milnorKInvolution k z)) :=
    ⟨by rw [monicIrreducibleResidue_mul_constants, hy.1, milnorKInvolution_milnorKRingMap,
        milnorKInvolution_involutive], fun d' ψ hne ↦ by
      rw [monicIrreducibleResidue_mul_constants, hy.2 d' ψ hne, zero_mul]⟩
  rw [simpleMilnorNorm_eq hyz, simpleMilnorNorm_eq hy, infinityResidueRing_mul_constants,
    milnorKInvolution_involutive, neg_mul]

end Stacks.Chow

end
