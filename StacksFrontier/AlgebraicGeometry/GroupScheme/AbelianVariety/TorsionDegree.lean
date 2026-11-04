module

public import StacksFrontier.AlgebraicGeometry.Cube.TheoremOfTheCube
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AlgClosedField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Torsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowCharFibre
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Multiplication by `n` and the torsion of an abelian variety

Let `A` be an abelian variety of dimension `g` over a field `k`. Multiplication by a nonzero
integer `n`, `[n] : A → A`, is finite locally free of rank `|n| ^ 2g`. From this follow the
surjectivity of `[n]`, the divisibility of `A(k)` for `k` algebraically closed, and the structure
of the torsion subgroups of `A(k)`.

## Main results

* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id`: `[n]` is finite locally free of degree
  `|n| ^ 2g` for `n ≠ 0`.
* `Stacks.Groupoids.surjective_zpow_id`: `[n]` is surjective for `n ≠ 0`.
* `Stacks.Groupoids.exists_pow_eq`: `A(k)` is divisible when `k` is algebraically closed.
* `Stacks.Groupoids.isFiniteLocallyFreeOfRank_torsion`: `A[n]` is finite locally free of degree
  `|n| ^ 2g` for `n ≠ 0`.
* `Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit`: `A(k)[n] ≅ (ℤ/nℤ) ^ 2g` for `n`
  invertible in an algebraically closed `k`.
* `Stacks.Groupoids.exists_torsionBy_char_pow_addEquiv`: `A(k)[p ^ m] ≅ (ℤ/p^mℤ) ^ f` for one
  `f ≤ g` and all `m`, over an algebraically closed `k` of characteristic `p > 0`.

## Implementation notes

Rational points are morphisms from the monoidal unit of `Over (Spec k)`, written additively for
their torsion subgroups.

## References

* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0C0Y](https://stacks.math.columbia.edu/tag/0C0Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- Let `k` be a field, let `A` be an abelian variety over `k` and let `[n] = (𝟙 A) ^ n : A ⟶ A`
be multiplication by a nonzero integer `n` in the group `A ⟶ A`. Then `[n]` is finite locally free
of degree `|n| ^ (2 * dim A)`. -/
@[stacks 0BFG "for n nonzero, the degree n^(2 dim A) read as |n|^(2 dim A): the source's \
statement fails for n = 0 when dim A >= 1, since [0] factors through the unit point and its \
fibre over the unit is all of A"]
theorem isFiniteLocallyFreeOfRank_zpow_id (n : ℤ) (hn : n ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ n).left
      (n.natAbs ^ (2 * abelianVarietyDimension A)) :=
  isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube A (hasTheoremOfTheCube k A) n hn

/-- Multiplication by a nonzero integer `n` on an abelian variety is surjective. -/
@[stacks 03RP "part (3), for every nonzero n", sga "7 IX 2.2.1" "more general"]
theorem surjective_zpow_id (n : ℤ) (hn : n ≠ 0) : Surjective ((𝟙 A : A ⟶ A) ^ n).left :=
  have := isFiniteLocallyFreeOfRank_zpow_id k A n hn
  Stacks.Morphisms.surjective_of_isFiniteLocallyFreeOfRank _
    (n.natAbs ^ (2 * abelianVarietyDimension A)) (pow_ne_zero _ (Int.natAbs_ne_zero.mpr hn))

/-- If `k` is algebraically closed, the group `A(k)` of rational points of an abelian variety is
divisible: for every `n ≥ 1`, every rational point is an `n`-th power. -/
@[stacks 03RP "part (4)", sga "3 VIII 7.11" "special case"]
theorem exists_pow_eq [IsAlgClosed k] (n : ℕ) (hn : n ≠ 0)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ A, y ^ n = x := by
  have := surjective_zpow_id k A n (mod_cast hn)
  obtain ⟨y, hy⟩ := exists_zpow_eq_of_surjective A (n : ℤ) x
  exact ⟨y, by rwa [zpow_natCast] at hy⟩

/-- For a nonzero integer `n`, the `n`-torsion group scheme `A[n] = Ker([n] : A → A)` of an
abelian variety `A` of dimension `g` is finite locally free of degree `|n| ^ 2g` over `k`. -/
@[stacks 03RP "part (5), for every nonzero n"]
theorem isFiniteLocallyFreeOfRank_torsion (n : ℤ) (hn : n ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (GrpObj.torsion A n).X.hom
      (n.natAbs ^ (2 * abelianVarietyDimension A)) :=
  have := isFiniteLocallyFreeOfRank_zpow_id k A n hn
  isFiniteLocallyFreeOfRank_torsion_hom A n _

/-- Let `A` be an abelian variety of dimension `g` over an algebraically closed field `k`, and `n`
a natural number invertible in `k`. Then the `n`-torsion `A(k)[n]` of the group of rational points
is isomorphic to `(ℤ/nℤ) ^ 2g`. -/
@[stacks 03RP "part (7)"]
theorem nonempty_torsionBy_addEquiv_of_isUnit [IsAlgClosed k] (n : ℕ) (hn : IsUnit (n : k)) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) n ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod n)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hunit : ∀ ℓ : ℕ, ℓ ∣ n → IsUnit (ℓ : k) := fun ℓ ⟨m, hm⟩ =>
    isUnit_of_mul_isUnit_left (by rw [← Nat.cast_mul, ← hm]; exact hn)
  refine nonempty_torsionBy_addEquiv_of_etale A n hn0 _ (fun ℓ hℓ _ x => ?_)
    (fun ℓ hℓ hd => ⟨(etale_torsion_iff k A ℓ).mpr (Or.inr (mod_cast hunit ℓ hd)), ?_⟩)
  · simpa only [zpow_natCast] using exists_pow_eq k A ℓ hℓ.ne_zero x
  · have := isFiniteLocallyFreeOfRank_torsion k A ℓ (mod_cast hℓ.ne_zero)
    rwa [Int.natAbs_natCast] at this

/-- Let `A` be an abelian variety of dimension `g` over an algebraically closed field `k` of
characteristic `p > 0`. There is an integer `0 ≤ f ≤ g` such that `A(k)[p ^ m] ≅ (ℤ/p^mℤ) ^ f` for
every `m` (for `m = 0` both sides are trivial). -/
@[stacks 03RP "part (8)"]
theorem exists_torsionBy_char_pow_addEquiv [IsAlgClosed k] (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ f ≤ abelianVarietyDimension A, ∀ m : ℕ, Nonempty
      (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((p ^ m : ℕ) : ℤ) ≃+
        (Fin f → ZMod (p ^ m))) := by
  have hpp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp)
  have := locallyOfFinitePresentation_zpow_id_left A (p : ℤ)
  have : LocallyOfFiniteType (GrpObj.torsion A p).X.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_torsion_left A p)
      inferInstance
  let T := AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (p : ℤ)
  have hle : Cardinal.mk T ≤ ((p ^ abelianVarietyDimension A : ℕ) : Cardinal) := by
    rw [Nat.cast_pow, Cardinal.mk_congr (torsionByEquivSections A p)]
    refine (cardinalMk_sections_le_of_isAlgClosed _).trans
      (le_trans ?_ (cardinalMk_fiber_multiplication_by_char_le A p hp))
    exact (Cardinal.mk_congr (Scheme.homeoOfIso ((isPullback_torsion_left A p).isoPullback ≪≫
      pullbackSymmetry _ _)).toEquiv).le
  have : Finite T := Cardinal.mk_lt_aleph0_iff.mp (hle.trans_lt (Cardinal.natCast_lt_aleph0))
  refine exists_torsionBy_prime_pow_addEquiv A p hpp _ (fun x => ?_) ?_
  · simpa only [zpow_natCast] using exists_pow_eq k A p hp.ne' x
  · rw [← Nat.cast_card (α := T)] at hle
    exact_mod_cast hle

end Stacks.Groupoids

end
