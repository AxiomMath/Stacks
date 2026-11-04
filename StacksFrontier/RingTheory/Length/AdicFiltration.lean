module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.RingTheory.Length.Finiteness

/-!
# Length is the sum of the residue dimensions of the adic graded pieces

Let `(R, m)` be a commutative local ring, let `k = R/m` be its residue field, and let `M` be an
`R`-module of finite length. Some power of `m` annihilates `M`, so the `m`-adic filtration
`M ⊇ m M ⊇ m² M ⊇ ⋯` reaches `0`, each graded piece `m^p M / m^{p+1} M` is a `k`-vector space,
and

`∑_{p ≥ 0} dim_k (m^p M / m^{p+1} M) = length_R M`.

The ring `R` is not assumed Noetherian.

## Main results

* `Stacks.Length.length_eq_sum_length_subquotient` — the general telescope: the length of `M` is
  the sum of the lengths of the subquotients of any finite filtration
  `M = N₀ ⊇ N₁ ⊇ ⋯ ⊇ Nₙ = 0`. No hypotheses on `R` or `M`; the identity holds in `ℕ∞`, so it is
  also true when both sides are infinite.
* `Stacks.Length.length_eq_sum_length_adicGradedPiece` — its `I`-adic instance, for any ideal `I`
  with `I^n M = 0`.
* `Stacks.Length.length_adicGradedPiece_eq_finrank` — a graded piece of the `m`-adic filtration
  of a finite-length module over a local ring is a finite-dimensional `k`-vector space whose
  dimension is its length over `R`.
* `Stacks.Length.length_eq_sum_finrank_adicGradedPiece` and
  `Stacks.Length.length_eq_finsum_finrank_adicGradedPiece` — **the identity above**, as a sum over
  `Finset.range n` for an exponent `n` with `m^n M = 0`, and as a sum over all `p ≥ 0`.
* `Stacks.Length.finsum_finrank_adicGradedPiece_eq_toNat_length` — the same identity between
  natural numbers.

## References

* [Stacks Project, Tag 00IW](https://stacks.math.columbia.edu/tag/00IW)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public section

namespace Stacks.Length

open IsLocalRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Telescoping a finite filtration -/

/-- Length is additive along one step `N₁ ≤ N₂` of a filtration: the subquotient `N₂ / N₁` is
formed inside `N₂`, as `Submodule.submoduleOf`. -/
theorem length_eq_add_length_quotient_submoduleOf {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) :
    Module.length R N₂ =
      Module.length R N₁ + Module.length R (↥N₂ ⧸ N₁.submoduleOf N₂) := by
  rw [← (Submodule.submoduleOfEquivOfLe h).length_eq]
  exact Module.length_eq_add_of_exact (N₁.submoduleOf N₂).subtype (N₁.submoduleOf N₂).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

/-- Telescoping the first `n` steps of a decreasing filtration: the length of `N₀` is the sum of
the lengths of the first `n` subquotients plus the length of `Nₙ`. -/
private theorem length_eq_sum_length_subquotient_add (N : ℕ → Submodule R M)
    (hstep : ∀ p, N (p + 1) ≤ N p) (n : ℕ) :
    Module.length R ↥(N 0) =
      (∑ p ∈ Finset.range n, Module.length R (↥(N p) ⧸ (N (p + 1)).submoduleOf (N p))) +
        Module.length R ↥(N n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, length_eq_add_length_quotient_submoduleOf (hstep n)]
    ring

/-- **Length is the sum of the lengths of the subquotients of a finite filtration.** If
`M = N₀ ⊇ N₁ ⊇ ⋯ ⊇ Nₙ = 0`, then `length_R M = ∑_{p < n} length_R (N_p / N_{p+1})`. -/
theorem length_eq_sum_length_subquotient (N : ℕ → Submodule R M)
    (hstep : ∀ p, N (p + 1) ≤ N p) (h0 : N 0 = ⊤) {n : ℕ} (hn : N n = ⊥) :
    Module.length R M =
      ∑ p ∈ Finset.range n, Module.length R (↥(N p) ⧸ (N (p + 1)).submoduleOf (N p)) := by
  have h := length_eq_sum_length_subquotient_add N hstep n
  rwa [h0, hn, Module.length_top, Module.length_bot, add_zero] at h

/-! ### The adic filtration -/

/-- The degree-`p` piece `I^p M / I^{p+1} M` of the `I`-adic filtration of `M`, formed as the
quotient of the submodule `I^p M` by `I • ⊤`. -/
abbrev adicGradedPiece (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (p : ℕ) :
    Type _ :=
  ↥(I ^ p • (⊤ : Submodule R M)) ⧸ I • (⊤ : Submodule R ↥(I ^ p • (⊤ : Submodule R M)))

/-- Inside a submodule `P`, the submodule carved out by `I • P` is `I • ⊤`. -/
theorem submoduleOf_smul (I : Ideal R) (P : Submodule R M) :
    (I • P).submoduleOf P = I • (⊤ : Submodule R ↥P) := by
  have h : Submodule.map P.subtype (I • (⊤ : Submodule R ↥P)) = I • P := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  show Submodule.comap P.subtype (I • P) = _
  rw [← h, Submodule.comap_map_eq_of_injective (Submodule.injective_subtype P)]

/-- The `I`-adic filtration is decreasing. -/
theorem pow_succ_smul_top_le (I : Ideal R) (p : ℕ) :
    I ^ (p + 1) • (⊤ : Submodule R M) ≤ I ^ p • (⊤ : Submodule R M) := by
  rw [pow_succ', Submodule.mul_smul]
  exact Submodule.smul_le_right

/-- The subquotient of the `I`-adic filtration at `p`, read inside `I^p M`, is `I • ⊤`. -/
theorem submoduleOf_pow_succ_smul_top (I : Ideal R) (p : ℕ) :
    (I ^ (p + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ p • (⊤ : Submodule R M)) =
      I • (⊤ : Submodule R ↥(I ^ p • (⊤ : Submodule R M))) := by
  rw [pow_succ', Submodule.mul_smul, submoduleOf_smul]

/-- **The length of `M` is the sum of the lengths of the graded pieces of its `I`-adic
filtration**, whenever `I^n M = 0`. -/
theorem length_eq_sum_length_adicGradedPiece (I : Ideal R) {n : ℕ}
    (hn : I ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.length R M =
      ∑ p ∈ Finset.range n, Module.length R (adicGradedPiece I M p) := by
  rw [length_eq_sum_length_subquotient (fun p ↦ I ^ p • (⊤ : Submodule R M))
    (fun p ↦ pow_succ_smul_top_le I p) (by simp) hn]
  exact Finset.sum_congr rfl fun p _ ↦
    (Submodule.quotEquivOfEq _ _ (submoduleOf_pow_succ_smul_top I p)).length_eq

/-! ### The dimensions over the residue field of a local ring -/

section IsLocalRing

variable [IsLocalRing R]

/-- The `p`-th graded piece of the `m`-adic filtration is a module over the residue field. -/
instance (p : ℕ) : Module (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) :=
  inferInstanceAs (Module (R ⧸ maximalIdeal R) (adicGradedPiece (maximalIdeal R) M p))

/-- The action of the residue field on a graded piece of the `m`-adic filtration is compatible
with the action of `R`. -/
instance (p : ℕ) : IsScalarTower R (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) :=
  inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (adicGradedPiece (maximalIdeal R) M p))

/-- The length of a graded piece of the `m`-adic filtration is the same over `R` and over the
residue field, the scalars acting through the surjection `R → k`. -/
theorem length_adicGradedPiece_eq_length_residueField (p : ℕ) :
    Module.length R (adicGradedPiece (maximalIdeal R) M p) =
      Module.length (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) :=
  Module.length_eq_of_surjective (R := ResidueField R) (S := R)
    (M := adicGradedPiece (maximalIdeal R) M p) IsLocalRing.residue_surjective

/-- A graded piece of the `m`-adic filtration of a module of finite length is a
finite-dimensional vector space over the residue field. -/
theorem finite_residueField_adicGradedPiece (hM : IsFiniteLength R M) (p : ℕ) :
    Module.Finite (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) := by
  have hsub : IsFiniteLength R ↥(maximalIdeal R ^ p • (⊤ : Submodule R M)) :=
    hM.of_injective (Submodule.injective_subtype _)
  have hQ : IsFiniteLength R (adicGradedPiece (maximalIdeal R) M p) :=
    hsub.of_surjective (Submodule.mkQ_surjective _)
  have hK : IsFiniteLength (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) := by
    rwa [← Module.length_ne_top_iff, ← length_adicGradedPiece_eq_length_residueField,
      Module.length_ne_top_iff]
  have : IsNoetherian (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hK).1
  exact Module.finite_def.mpr (IsNoetherian.noetherian ⊤)

/-- The length over `R` of a graded piece of the `m`-adic filtration of a module of finite length
is its dimension over the residue field. -/
theorem length_adicGradedPiece_eq_finrank (hM : IsFiniteLength R M) (p : ℕ) :
    Module.length R (adicGradedPiece (maximalIdeal R) M p) =
      (Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) : ℕ∞) := by
  have := finite_residueField_adicGradedPiece hM p
  rw [length_adicGradedPiece_eq_length_residueField, Module.length_eq_finrank]

/-- Beyond an exponent that annihilates `M`, the graded pieces of the `m`-adic filtration
vanish. -/
theorem finrank_adicGradedPiece_eq_zero {n : ℕ}
    (hn : maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥) {p : ℕ} (hp : n ≤ p) :
    Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) = 0 := by
  have hbot : maximalIdeal R ^ p • (⊤ : Submodule R M) = ⊥ :=
    le_bot_iff.mp (hn ▸ Submodule.smul_mono (Ideal.pow_le_pow_right hp) le_rfl)
  have : Subsingleton ↥(maximalIdeal R ^ p • (⊤ : Submodule R M)) := by
    rw [hbot]; infer_instance
  have : Subsingleton (adicGradedPiece (maximalIdeal R) M p) :=
    Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
  exact Module.finrank_zero_of_subsingleton

/-- **Length additivity along the `m`-adic filtration.** For a module `M` of finite length over a
local ring `(R, m)` with residue field `k`, and any `n` with `m^n M = 0`,

`length_R M = ∑_{p < n} dim_k (m^p M / m^{p+1} M)`. -/
theorem length_eq_sum_finrank_adicGradedPiece (hM : IsFiniteLength R M) {n : ℕ}
    (hn : maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.length R M =
      ∑ p ∈ Finset.range n,
        (Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) : ℕ∞) := by
  rw [length_eq_sum_length_adicGradedPiece (maximalIdeal R) hn]
  exact Finset.sum_congr rfl fun p _ ↦ length_adicGradedPiece_eq_finrank hM p

/-- The graded pieces of the `m`-adic filtration have nonzero dimension only below an exponent
`n` that annihilates `M`. -/
private theorem support_finrank_adicGradedPiece_subset {n : ℕ}
    (hn : maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥) :
    (Function.support fun p : ℕ ↦
      Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p)) ⊆
      ↑(Finset.range n) := by
  intro p hp
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  exact hp (finrank_adicGradedPiece_eq_zero hn (not_lt.mp hle))

/-- **Length additivity along the `m`-adic filtration**, summed over all `p ≥ 0`. For a module `M`
of finite length over a local ring `(R, m)` with residue field `k`,

`∑_{p ≥ 0} dim_k (m^p M / m^{p+1} M) = length_R M`.

The sum is finite because `m^p M = 0` for large `p`. -/
theorem length_eq_finsum_finrank_adicGradedPiece (hM : IsFiniteLength R M) :
    Module.length R M =
      ∑ᶠ p : ℕ,
        (Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) : ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength R M hM
  rw [length_eq_sum_finrank_adicGradedPiece hM hn]
  exact (finsum_eq_sum_of_support_subset _
    ((Function.support_comp_subset (g := ((↑) : ℕ → ℕ∞)) Nat.cast_zero _).trans
      (support_finrank_adicGradedPiece_subset hn))).symm

/-- **Length additivity along the `m`-adic filtration**, as an identity of natural numbers. -/
theorem finsum_finrank_adicGradedPiece_eq_toNat_length (hM : IsFiniteLength R M) :
    ∑ᶠ p : ℕ, Module.finrank (ResidueField R) (adicGradedPiece (maximalIdeal R) M p) =
      (Module.length R M).toNat := by
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength R M hM
  rw [finsum_eq_sum_of_support_subset _ (support_finrank_adicGradedPiece_subset hn),
    length_eq_sum_finrank_adicGradedPiece hM hn, ← Nat.cast_sum, ENat.toNat_natCast]

end IsLocalRing

end Stacks.Length

end
