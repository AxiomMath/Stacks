module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSeparableSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleInvertible
public import StacksFrontier.GroupTheory.TorsionOfDivisible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The `n`-torsion of the rational points of an abelian variety, from the degree of `[n]`

Let `A` be a group scheme over an algebraically closed field `k`, and suppose that
multiplication by `d` on `A` is finite locally free of rank `r` and étale. Then the fibre of
`[d]` over the unit is a finite étale `k`-scheme of rank `r`, and its `k`-points are the
rational points of `A` killed by `d`; so `A(k)[d]` has exactly `r` elements.

Combined with the divisibility of `A(k)` (clause (4) of [Stacks, Tag 03RP]) and the group theory
of `StacksFrontier/GroupTheory/TorsionOfDivisible.lean`, this is the passage from [Stacks, Tag 0BFG]
and [Stacks, Tag 0BFH] to clause (7) of [Stacks, Tag 03RP]: if `n` is invertible in `k`, then
`A(k)[n] ≅ (𝐙/n𝐙)^{2 dim A}`.

## Main results

* `Stacks.Morphisms.natCard_sections_eq_of_etale_isFiniteLocallyFreeOfRank`: a finite locally
  free étale morphism of rank `r` to the spectrum of an algebraically closed field has exactly `r`
  sections.
* `Stacks.Groupoids.natCard_pow_eq_one_eq`: `#{a ∈ A(k) | a ^ d = 1} = r` when `[d]` is finite
  locally free of rank `r` and étale.
* `Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank`: clause (7) of
  [Stacks, Tag 03RP] from the rank of `[p]` at the primes `p ∣ n`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Morphisms

/-- **A finite étale scheme of rank `r` over an algebraically closed field has `r` rational
points.** If `f : Z ⟶ Spec K` is étale and finite locally free of rank `r`, with `K`
algebraically closed, then `f` has exactly `r` sections. -/
@[sga "3 VIII 2.1" "Forward direction"]
theorem natCard_sections_eq_of_etale_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    [IsAlgClosed K] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (r : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f r) (hetale : Etale f) :
    Nat.card {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} = r := by
  obtain ⟨hfin, hle⟩ := finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank f r hf
  obtain ⟨K', _, _, _, _, σ, hinj, hσ⟩ :=
    exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank f r hf hetale
  let e : K ≃+* K' := RingEquiv.ofBijective (algebraMap K K')
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let g : CommRingCat.of K' ≅ CommRingCat.of K := e.symm.toCommRingCatIso
  have he : CommRingCat.ofHom (algebraMap K K') ≫ g.hom = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  let τ : Fin r → {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} := fun j =>
    ⟨Spec.map g.hom ≫ σ j, by
      rw [Category.assoc, hσ j, ← Spec.map_comp, he, Spec.map_id]⟩
  refine hle.antisymm ?_
  simpa using Nat.card_le_card_of_injective τ fun i j h =>
    hinj ((cancel_epi (Spec.map g.hom)).1
      (congrArg Subtype.val h))

end Stacks.Morphisms

namespace Stacks.Groupoids

open Stacks.Morphisms (IsFiniteLocallyFreeOfRank)

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- The unit of the group of rational points is the unit section. -/
theorem one_eq_unit : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = η[A] := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

/-- A rational point composed with multiplication by `d` is its `d`-th power. -/
theorem comp_zpow_id (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (d : ℤ) :
    a ≫ (𝟙 A : A ⟶ A) ^ d = a ^ d := by
  rw [GrpObj.comp_zpow, Category.comp_id]

noncomputable section

/-- **The rational points killed by `d` are the sections of the fibre of `[d]` over the unit.** -/
def powEqOneEquivSections (d : ℤ) :
    {a : 𝟙_ (Over (Spec (.of k))) ⟶ A // a ^ d = 1} ≃
      {σ : Spec (CommRingCat.of k) ⟶ pullback ((𝟙 A : A ⟶ A) ^ d).left η[A].left //
        σ ≫ pullback.snd _ _ = 𝟙 _} where
  toFun a := ⟨pullback.lift a.1.left (𝟙 _) (by
      rw [← Over.comp_left, comp_zpow_id, a.2, one_eq_unit, Category.id_comp]),
    pullback.lift_snd _ _ _⟩
  invFun σ := ⟨Over.homMk (σ.1 ≫ pullback.fst _ _) (by
      have h1 : pullback.fst ((𝟙 A : A ⟶ A) ^ d).left η[A].left ≫ A.hom =
          pullback.snd ((𝟙 A : A ⟶ A) ^ d).left η[A].left ≫ (𝟙_ (Over (Spec (.of k)))).hom := by
        rw [← zpow_id_left_comp_hom A d, ← Category.assoc, pullback.condition, Category.assoc,
          Over.w]
      rw [Category.assoc, h1, ← Category.assoc, σ.2]
      exact Category.id_comp _), by
    rw [← comp_zpow_id, one_eq_unit]
    ext
    rw [Over.comp_left]
    change (σ.1 ≫ pullback.fst _ _) ≫ _ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, σ.2, Category.id_comp]⟩
  left_inv a := by
    ext
    exact pullback.lift_fst _ _ _
  right_inv σ := Subtype.ext <| pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans σ.2.symm)

end

variable [IsAlgClosed k]

/-- **`#A(k)[d] = r`** when multiplication by `d` is finite locally free of rank `r` and étale:
the rational points killed by `d` are the rational points of the fibre of `[d]` over the unit,
which is finite étale of rank `r` over the algebraically closed field `k`. -/
theorem natCard_pow_eq_one_eq (d : ℤ) (r : ℕ)
    [IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left r]
    (hetale : Etale ((𝟙 A : A ⟶ A) ^ d).left) :
    Nat.card {a : 𝟙_ (Over (Spec (.of k))) ⟶ A // a ^ d = 1} = r := by
  rw [Nat.card_congr (powEqOneEquivSections A d)]
  exact Stacks.Morphisms.natCard_sections_eq_of_etale_isFiniteLocallyFreeOfRank _ r
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback ((𝟙 A : A ⟶ A) ^ d).left η[A].left))
    (by have := hetale; infer_instance)

/-- **Multiplication by an integer invertible in `k` is finite**: for an abelian variety
`A` over `k` and `n : ℕ` invertible in `k`, the underlying morphism of multiplication by `n` on
`A` is finite. This is the finiteness half of [Stacks, Tag 0BFG] for such integers, with no
ample module. -/
theorem isFinite_natCast_zpow_id_left_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hn : IsUnit (n : k)) : IsFinite ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := by
  have := etale_natCast_zpow_id_left_of_isUnit A n hn
  exact (isFinite_zpow_id_left_iff_locallyQuasiFinite A (n : ℤ)).2 inferInstance

/-- **Multiplication by an integer invertible in `k` is finite locally free**: finite by
`Stacks.Groupoids.isFinite_natCast_zpow_id_left_of_isUnit` and flat because étale. This is
[Stacks, Tag 0BFG] for such integers except for the value of the degree. -/
theorem isFiniteLocallyFree_zpow_id_left_of_isUnit [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left := by
  have := isFinite_natCast_zpow_id_left_of_isUnit A n hn
  have := flat_zpow_id_left_of_isUnit A n hn
  exact isFiniteLocallyFree_of_isFinite_of_flat A _

omit [IsAlgClosed k] in
/-- The `n`-torsion of `Additive A(k)`, counted as rational points killed by `n`. -/
theorem natCard_torsionBy_eq [IsCommMonObj A] (n : ℕ) :
    Nat.card (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ)) =
      Nat.card {a : 𝟙_ (Over (Spec (.of k))) ⟶ A // a ^ (n : ℤ) = 1} :=
  Nat.card_congr <| Equiv.subtypeEquiv Additive.toMul fun x => by
    rw [AddSubgroup.torsionBy.nsmul_iff, zpow_natCast, ← toMul_nsmul,
      ← Additive.toMul.injective.eq_iff, toMul_zero]

/-- **Clause (7) of [Stacks, Tag 03RP], from the degree of `[p]`.** Let `A` be an abelian variety
over an algebraically closed field `k` and let `n` be invertible in `k`. If for every prime `p ∣ n`
multiplication by `p` is finite locally free of degree `p ^ N` — which is [Stacks, Tag 0BFG] with
`N = 2 dim A` — then `A(k)[n] ≅ (𝐙/n𝐙)^N`.

Multiplication by `p` is étale because `p` is invertible in `k`
(`Stacks.Groupoids.etale_natCast_zpow_id_left_of_isUnit`), so `#A(k)[p] = p ^ N` by
`Stacks.Groupoids.natCard_pow_eq_one_eq`; multiplication by `n` is flat for the same reason, so
`A(k)` is `n`-divisible by `Stacks.Groupoids.exists_pow_eq_of_flat`; and
`AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible_of_card` concludes. -/
theorem nonempty_torsionBy_addEquiv_of_isFiniteLocallyFreeOfRank
    [AlgebraicGeometry.IsAbelianVariety k A] (n N : ℕ) (hn : IsUnit (n : k))
    (hrank : ∀ p : ℕ, p.Prime → p ∣ n →
      IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ (p : ℤ)).left (p ^ N)) :
    letI : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (n : ℤ) ≃+
      (Fin N → ZMod n)) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine AddCommGroup.nonempty_torsionBy_addEquiv_of_divisible_of_card hn0 (fun x => ?_)
    (fun p hp hpn => ?_)
  · obtain ⟨b, hb⟩ := exists_pow_eq_of_flat A n (flat_zpow_id_left_of_isUnit A n hn) x.toMul
    exact ⟨Additive.ofMul b, Additive.toMul.injective (by rw [toMul_nsmul, toMul_ofMul, ← hb])⟩
  · have := hrank p hp hpn
    rw [natCard_torsionBy_eq]
    exact natCard_pow_eq_one_eq A p (p ^ N)
      (etale_natCast_zpow_id_left_of_isUnit A p (isUnit_of_dvd_unit (Nat.cast_dvd_cast hpn) hn))

end Stacks.Groupoids
