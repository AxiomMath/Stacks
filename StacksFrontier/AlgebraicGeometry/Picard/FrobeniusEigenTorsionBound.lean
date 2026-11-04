module

public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusFixedTorsion

/-!
# The cyclotomic Frobenius eigenvectors in `Pic(Y_k̄)[ℓⁿ]` are bounded

Let `Y` be a smooth proper geometrically irreducible curve over a finite field `k` with `q`
elements, `σ` the Frobenius of `Pic(Y_k̄)` and `ℓ` a prime. Given, for every `n`, a
left-nondegenerate pairing `eₙ` on `Pic(Y_k̄)[ℓⁿ]` with values in `ℤ/ℓⁿ` with
`eₙ(σa, σb) = q · eₙ(a, b)` (the Weil pairing) and the finiteness of `Pic(Y_k̄)[ℓⁿ]`, the kernel of
`σ - q` on `Pic(Y_k̄)[ℓⁿ]` has at most as many elements as the kernel of `σ - 1`
(`Stacks.Picard.natCard_ker_sub_smul_le`), which is bounded independently of `n`
(`Stacks.Picard.exists_natCard_ker_frobeniusPicardHom_sub_id_le`).

## Main results

* `Stacks.Picard.exists_natCard_ker_frobeniusPicardHom_sub_card_le`: the kernel of `σ - q` on
  `Pic(Y_k̄)[ℓⁿ]` has cardinality bounded independently of `n`.
* `Stacks.Picard.exists_forall_encard_le_of_injOn`: sets mapping injectively into the
  `ℓⁿ`-torsion classes `z` with `σ z = q z` have cardinality bounded independently of `n`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  [IsProper Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve k Y.hom]

/-- Given the finiteness of `Pic(Y_k̄)[ℓⁿ]` and left-nondegenerate pairings `eₙ` on it with values
in `ℤ/ℓⁿ` satisfying `eₙ(σa, σb) = q · eₙ(a, b)`, the kernel of `σ - q` on `Pic(Y_k̄)[ℓⁿ]` has
cardinality bounded independently of `n`. -/
theorem exists_natCard_ker_frobeniusPicardHom_sub_card_le (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (hfin : ∀ n : ℕ, Finite (Submodule.torsionBy ℤ
      (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)))
    (hunit : ∀ n : ℕ, IsUnit ((Fintype.card k : ℤ) : ZMod (ℓ ^ n)))
    (hWeil : ∀ n : ℕ, ∃ e : Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ
          (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
          ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (torsionByRestrict (frobeniusPicardHom Y) _ a)
          (torsionByRestrict (frobeniusPicardHom Y) _ b) = (Fintype.card k : ℤ) • e a b) :
    ∃ C : ℕ, ∀ n : ℕ, Nat.card (torsionByRestrict (frobeniusPicardHom Y) ((ℓ : ℤ) ^ n) -
      (Fintype.card k : ℤ) • AddMonoidHom.id (Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n))).ker ≤ C := by
  obtain ⟨C, hC⟩ := exists_natCard_ker_frobeniusPicardHom_sub_id_le Y ℓ hℓ
  refine ⟨C, fun n => ?_⟩
  have := hfin n
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ⟩
  obtain ⟨e, he₀, he⟩ := hWeil n
  exact (natCard_ker_sub_smul_le e he₀ _ _ (hunit n) he).trans (hC n)

/-- Under the hypotheses of `Stacks.Picard.exists_natCard_ker_frobeniusPicardHom_sub_card_le`, if
`Φₙ` maps `Sₙ` injectively to `ℓⁿ`-torsion classes `z` with `σ z = q z`, then the `Sₙ` have
cardinality bounded independently of `n`. -/
theorem exists_forall_encard_le_of_injOn (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (hfin : ∀ n : ℕ, Finite (Submodule.torsionBy ℤ
      (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)))
    (hunit : ∀ n : ℕ, IsUnit ((Fintype.card k : ℤ) : ZMod (ℓ ^ n)))
    (hWeil : ∀ n : ℕ, ∃ e : Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ
          (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
          ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (torsionByRestrict (frobeniusPicardHom Y) _ a)
          (torsionByRestrict (frobeniusPicardHom Y) _ b) = (Fintype.card k : ℤ) • e a b)
    {β : ℕ → Type*} (S : ∀ n, Set (β n))
    (Φ : ∀ n, β n → ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y))
    (hinj : ∀ n, Set.InjOn (Φ n) (S n))
    (htor : ∀ n, ∀ s ∈ S n, ((ℓ : ℤ) ^ n) • Φ n s = 0)
    (heig : ∀ n, ∀ s ∈ S n, frobeniusPicardHom Y (Φ n s) = (Fintype.card k : ℤ) • Φ n s) :
    ∃ C : ℕ, ∀ n, (S n).encard ≤ C := by
  obtain ⟨C, hC⟩ := exists_natCard_ker_frobeniusPicardHom_sub_card_le Y ℓ hℓ hfin hunit hWeil
  refine ⟨C, fun n => ?_⟩
  have := hfin n
  set M := Submodule.torsionBy ℤ
    (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)
  set K := (torsionByRestrict (frobeniusPicardHom Y) ((ℓ : ℤ) ^ n) -
    (Fintype.card k : ℤ) • AddMonoidHom.id M).ker
  have hsub : Φ n '' S n ⊆ Set.range fun z : K => ((z : M) :
      ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) := by
    rintro _ ⟨s, hs, rfl⟩
    have hm : Φ n s ∈ M := (Submodule.mem_torsionBy_iff _ _).2 (htor n s hs)
    refine ⟨⟨⟨Φ n s, hm⟩, ?_⟩, rfl⟩
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
    apply Subtype.ext
    simp only [torsionByRestrict_apply, AddMonoidHom.smul_apply]
    exact heig n s hs
  calc (S n).encard = (Φ n '' S n).encard := ((hinj n).encard_image).symm
    _ ≤ (Set.range fun z : K => ((z : M) :
        ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y))).encard :=
        Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set K).encard := by
        rw [← Set.image_univ]
        exact Set.encard_image_le _ _
    _ = Nat.card K := by
        rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ C := by exact_mod_cast hC n

end Stacks.Picard
