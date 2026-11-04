module

public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.InvariantFactorCount

/-!
# Transferring a torsion exponent across equal lengths

Let `A` be a discrete valuation ring with uniformizer `π`. A finite `A`-module `Z` sitting in an
exact sequence

`M₀ --π^m--> M₀ --> Z --> M₁ --π^m--> M₁`

is an extension of `M₁[π ^ m]` by `M₀ ⧸ π ^ m M₀`, so its length is the sum of theirs. Comparing
two such extensions at two consecutive exponents `m - 1` and `m` therefore compares the numbers
of invariant factors of exponent at least `m`, which is how a bound on the torsion exponent of
one `M₁` transfers to another. Unlike
`Stacks.AlgebraicGeometry.FreenessOverDVR.pow_smul_torsionBy_eq_bot_of_linearEquiv_mod_pow`,
nothing here asks for the extensions to split: only their lengths are compared.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `length_eq_length_quotient_add_length_torsionBy`: the length of the middle term of the exact
  sequence above.
* `pow_smul_torsionBy_eq_bot_of_length_eq`: the transfer of the exponent bound along an equality
  of such lengths at two consecutive exponents.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public section

universe u v w

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {A : Type u} [CommRing A] {π : A}

section Exact

variable {M₀ : Type v} [AddCommGroup M₀] [Module A M₀] {M₁ : Type v} [AddCommGroup M₁]
  [Module A M₁] {Z : Type w} [AddCommGroup Z] [Module A Z]

/-- **The length of the middle term of `M₀ --π^m--> M₀ --> Z --> M₁ --π^m--> M₁`.** The
sequence presents `Z` as an extension of the `π ^ m`-torsion of `M₁` by `M₀ ⧸ π ^ m M₀`. -/
theorem length_eq_length_quotient_add_length_torsionBy (m : ℕ) (c : M₀ →ₗ[A] Z)
    (δ : Z →ₗ[A] M₁) (h₁ : Function.Exact ((π ^ m) • (LinearMap.id : M₀ →ₗ[A] M₀)) c)
    (h₂ : Function.Exact c δ)
    (h₃ : Function.Exact δ ((π ^ m) • (LinearMap.id : M₁ →ₗ[A] M₁))) :
    Module.length A Z =
      Module.length A (M₀ ⧸ Ideal.span {π} ^ m • (⊤ : Submodule A M₀)) +
        Module.length A (Submodule.torsionBy A M₁ (π ^ m)) := by
  have hker : LinearMap.ker c = Ideal.span {π} ^ m • (⊤ : Submodule A M₀) := by
    rw [LinearMap.exact_iff.1 h₁, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]
  have hrange : LinearMap.range δ = Submodule.torsionBy A M₁ (π ^ m) := by
    rw [← LinearMap.exact_iff.1 h₃]
    ext x
    simp [Submodule.mem_torsionBy_iff]
  rw [Module.length_eq_add_of_exact (LinearMap.range c).subtype δ.rangeRestrict
      (Submodule.subtype_injective _) δ.surjective_rangeRestrict ?_,
    ← (LinearMap.quotKerEquivRange c).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq, (LinearEquiv.ofEq _ _ hrange).length_eq]
  intro z
  rw [Set.mem_range, LinearMap.rangeRestrict, Subtype.ext_iff, LinearMap.codRestrict_apply,
    ZeroMemClass.coe_zero, h₂ z]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨c y, y, rfl⟩, rfl⟩
  · rintro ⟨⟨_, y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

end Exact

section DiscreteValuationRing

variable [IsDomain A] [IsDiscreteValuationRing A]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The length of `P ⧸ π ^ k P` is the length of its `π ^ k`-torsion: all of it. -/
theorem length_quotient_eq_torsionLength (P : Type v) [AddCommGroup P] [Module A P] (k : ℕ) :
    Module.length A (P ⧸ Ideal.span {π} ^ k • (⊤ : Submodule A P)) =
      torsionLength π k (P ⧸ Ideal.span {π} ^ k • (⊤ : Submodule A P)) := by
  have htop : Submodule.torsionBy A (P ⧸ Ideal.span {π} ^ k • (⊤ : Submodule A P)) (π ^ k) =
      ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [torsionLength, htop, Module.length_top]

/-- **Transfer of a torsion exponent across equal lengths.** Let `H, H', G, G'` be finite
modules over a discrete valuation ring with uniformizer `π`, with `H` and `G` of the same free
rank, and suppose that at the two exponents `k = m - 1` and `k = m` the length of
`H ⧸ π ^ k H` plus that of `H'[π ^ k]` equals the length of `G ⧸ π ^ k G` plus that of
`G'[π ^ k]`. If `π ^ (m - 1)` annihilates `G[π ^ m]` and `G'[π ^ m]`, it annihilates
`H'[π ^ m]`. -/
theorem pow_smul_torsionBy_eq_bot_of_length_eq (hπ : Irreducible π)
    {H H' G G' : Type v}
    [AddCommGroup H] [Module A H] [Module.Finite A H]
    [AddCommGroup H'] [Module A H'] [Module.Finite A H']
    [AddCommGroup G] [Module A G] [Module.Finite A G]
    [AddCommGroup G'] [Module A G'] [Module.Finite A G']
    {m : ℕ} (hm : 1 ≤ m)
    (hG : Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A G (π ^ m) = ⊥)
    (hG' : Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A G' (π ^ m) = ⊥)
    (hrank : Module.finrank A (H ⧸ Submodule.torsion A H) =
      Module.finrank A (G ⧸ Submodule.torsion A G))
    (hlen : ∀ k : ℕ, m - 1 ≤ k → k ≤ m →
      Module.length A (H ⧸ Ideal.span {π} ^ k • (⊤ : Submodule A H)) + torsionLength π k H' =
        Module.length A (G ⧸ Ideal.span {π} ^ k • (⊤ : Submodule A G)) +
          torsionLength π k G') :
    Ideal.span {π} ^ (m - 1) • Submodule.torsionBy A H' (π ^ m) = ⊥ := by
  obtain ⟨ιH, hιH, lH, -, hQH⟩ := exists_invariantFactors hπ H
  obtain ⟨ιH', hιH', lH', hTH', -⟩ := exists_invariantFactors hπ H'
  obtain ⟨ιG, hιG, lG, hTG, hQG⟩ := exists_invariantFactors hπ G
  obtain ⟨ιG', hιG', lG', hTG', -⟩ := exists_invariantFactors hπ G'
  have key : ∀ k : ℕ, m - 1 ≤ k → k ≤ m →
      (∑ i, min (lH i) k) + (∑ i, min (lH' i) k)
        = (∑ i, min (lG i) k) + (∑ i, min (lG' i) k) := by
    intro k hk₁ hk₂
    have hL := hlen k hk₁ hk₂
    rw [length_quotient_eq_torsionLength, length_quotient_eq_torsionLength, hQH k k le_rfl,
      hQG k k le_rfl, hTH' k, hTG' k, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj, hrank,
      add_assoc, add_assoc] at hL
    exact Nat.add_left_cancel hL
  have e1 := key m (by omega) le_rfl
  have e2 := key (m - 1) le_rfl (by omega)
  have hGs := (pow_smul_torsionBy_eq_bot_iff_torsionLength_eq hπ G hm).1 hG
  have hG's := (pow_smul_torsionBy_eq_bot_iff_torsionLength_eq hπ G' hm).1 hG'
  rw [hTG m, hTG (m - 1), Nat.cast_inj] at hGs
  rw [hTG' m, hTG' (m - 1), Nat.cast_inj] at hG's
  have hmono : ∀ (ι : Type u) [Fintype ι] (l : ι → ℕ),
      (∑ i, min (l i) (m - 1)) ≤ ∑ i, min (l i) m := fun ι _ l =>
    Finset.sum_le_sum fun i _ => by omega
  have mH := hmono ιH lH
  have mH' := hmono ιH' lH'
  refine (pow_smul_torsionBy_eq_bot_iff_torsionLength_eq hπ H' hm).2 ?_
  rw [hTH' m, hTH' (m - 1), Nat.cast_inj]
  omega

end DiscreteValuationRing

end Stacks.AlgebraicGeometry.FreenessOverDVR
