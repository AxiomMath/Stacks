module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.AlgClosedDivisiblePoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an invertible integer on an abelian variety is onto

Multiplication by an integer `d` on a group scheme `A` is the `d`-th power `[d]` of the identity
in the group `A ⟶ A` of morphisms into the group object. This file proves, for `d` invertible in
the ground field `k`, the two parts of [Stacks, Tag 03RP] saying that `[d]` is onto: `[d]` is
surjective (clause (3)), and over an algebraically closed field every rational point is a `d`-th
power (clause (4)).

## Main results

* `Stacks.Groupoids.surjective_zpow_id_left_of_flat`: if `[d]` is flat it is surjective.
* `Stacks.Groupoids.exists_zpow_eq_of_flat`: over an algebraically closed field, if `[d]` is
  flat then every rational point is a `d`-th power.
* `Stacks.Groupoids.exists_zpow_eq_of_isUnit`, `Stacks.Groupoids.exists_pow_eq_of_isUnit` and
  `Stacks.Groupoids.exists_nsmul_eq_of_isUnit`: clause (4) of Tag 03RP for `d` invertible in `k`,
  the last in the additive notation of `Additive (𝟙_ _ ⟶ A)`.
* `Stacks.Groupoids.exists_nsmul_eq_of_surjective_of_isUnit`: the transport of clause (4) along a
  surjective homomorphism from `A(k)` onto an additive group.

## Implementation notes

**Clause (3).** The image of `[d]` is closed because `[d]` is proper
(`Stacks.Groupoids.isProper_zpow_id_left`) and open because a flat morphism locally of finite
presentation is open ([Stacks, Tag 01UA]); it is nonempty, and the underlying scheme of an
abelian variety is integral, hence preconnected. For `d` invertible in `k`, `[d]` is étale by
[Stacks, Tag 0BFH] (`Stacks.Groupoids.etale_zpow_id_left_of_isUnit`), hence flat.

Clause (3) for `d` invertible in `k` is `Stacks.Groupoids.surjective_zpow_id_left_of_isUnit`.

**Clause (4).** A surjective `[d]` lifts every rational point to a rational point over an
algebraically closed field
(`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed`). The group of
rational points is Mathlib's `CategoryTheory.GrpObj.Hom.group` on `𝟙_ (Over (Spec k)) ⟶ A`, and
`CategoryTheory.GrpObj.comp_zpow` identifies composition with `[d]` with the `d`-th power.

The case of `d` not invertible in `k` needs [Stacks, Tag 0BFG] and is not treated here.

The clauses need flatness of `[d]`; that hypothesis is discharged here for `d` invertible in `k`.

## References

* [Stacks Project, Proposition 39.9.11 (Tag 03RP)](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Multiplication by an integer `d` on an abelian variety is surjective as soon as it is
flat.**

The image is closed because `[d]` is proper, open because `[d]` is flat and locally of finite
presentation, and nonempty; the underlying scheme is integral, hence preconnected, so a nonempty
clopen subset is everything.  Flatness of `[d]` is the only hypothesis: properness and local
finite presentation hold for every `d` on an abelian variety. -/
theorem surjective_zpow_id_left_of_flat [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hflat : Flat ((𝟙 A : A ⟶ A) ^ d).left) :
    Surjective ((𝟙 A : A ⟶ A) ^ d).left := by
  let := hflat
  have hproper := isProper_zpow_id_left A d
  have hfp := locallyOfFinitePresentation_zpow_id_left A d
  have hcl : IsClosed (Set.range ⇑((𝟙 A : A ⟶ A) ^ d).left) :=
    ((𝟙 A : A ⟶ A) ^ d).left.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range ⇑((𝟙 A : A ⟶ A) ^ d).left) :=
    (Scheme.Hom.isOpenMap _).isOpen_range
  refine ⟨?_⟩
  rw [← Set.range_eq_univ]
  exact IsClopen.eq_univ ⟨hcl, hop⟩ (Set.range_nonempty _)

/-- Multiplication by `d` on an abelian variety is surjective as soon as it is finite locally
free, which is the conclusion of [Stacks, Tag 0BFG]. -/
theorem surjective_zpow_id_left_of_isFiniteLocallyFree
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hfl : Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left) :
    Surjective ((𝟙 A : A ⟶ A) ^ d).left := by
  let := hfl
  exact surjective_zpow_id_left_of_flat A d (Stacks.Morphisms.IsFiniteLocallyFree.flat _)

/-- **Over an algebraically closed field every rational point of an abelian variety is a `d`-th
power in the group of rational points, as soon as `[d]` is flat.**

A flat `[d]` is surjective (`Stacks.Groupoids.surjective_zpow_id_left_of_flat`), and a surjective
`[d]` lifts every rational point to a rational point
(`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed`); composition with
`[d]` is the `d`-th power in the group of rational points. -/
theorem exists_zpow_eq_of_flat [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hflat : Flat ((𝟙 A : A ⟶ A) ^ d).left) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, a = b ^ d := by
  obtain ⟨g, hg, hgd⟩ := exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed A d
    (surjective_zpow_id_left_of_flat A d hflat) a.left (Over.w a)
  refine ⟨Over.homMk g hg, ?_⟩
  have hbd : (Over.homMk g hg : 𝟙_ (Over (Spec (.of k))) ⟶ A) ^ d =
      Over.homMk g hg ≫ (𝟙 A : A ⟶ A) ^ d := by
    rw [GrpObj.comp_zpow, Category.comp_id]
  rw [hbd]
  exact Over.OverMorphism.ext hgd.symm

/-- The natural-number form of [Stacks, Tag 03RP], clause (4): over an algebraically closed field
every rational point of an abelian variety is an `n`-th power, provided `[n]` is flat. -/
theorem exists_pow_eq_of_flat [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ)
    (hflat : Flat ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, a = b ^ n := by
  obtain ⟨b, hb⟩ := exists_zpow_eq_of_flat A (n : ℤ) hflat a
  exact ⟨b, by rwa [zpow_natCast] at hb⟩

/-- **The `n`-divisibility that clause (4) of [Stacks, Tag 03RP] gives a group of the form
`A(k)`, transported to any additive group it surjects onto.** If `φ` carries multiplication in
the rational points of an abelian variety to addition in an additive group `P` and is onto, then
every element of `P` is `n` times an element of `P`, provided `[n]` is flat.

This is the shape in which the consumers of the tag use clause (4): for the Picard group of a
curve `φ` would be the identification of `Pic⁰(X)` with the rational points of the Picard scheme
of [Stacks, Tag 0BA0], which this library does not have. -/
theorem exists_nsmul_eq_of_surjective [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hflat : Flat ((𝟙 A : A ⟶ A) ^ (n : ℤ)).left)
    {P : Type*} [AddCommGroup P] (φ : (𝟙_ (Over (Spec (.of k))) ⟶ A) → P)
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ) (x : P) :
    ∃ y, x = n • y := by
  have hone : φ 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    refine add_left_cancel (a := φ 1) ?_
    rw [add_zero, ← h]
  have hpow : ∀ (m : ℕ) (c : 𝟙_ (Over (Spec (.of k))) ⟶ A), φ (c ^ m) = m • φ c := by
    intro m c
    induction m with
    | zero => rw [pow_zero, zero_smul, hone]
    | succ m ih => rw [pow_succ, hmul, ih, succ_nsmul]
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := exists_pow_eq_of_flat A n hflat a
  exact ⟨φ b, hpow n b⟩

/-- **Stacks Project, Tag 03RP, clause (4), for `d` invertible in `k`.** Over an algebraically
closed field `k`, every rational point of an abelian variety is a `d`-th power, for every
integer `d` invertible in `k`. -/
theorem exists_zpow_eq_of_isUnit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (d : ℤ) (hd : IsUnit (d : k)) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, a = b ^ d :=
  exists_zpow_eq_of_flat A d
    (Etale.iff_flat_and_formallyUnramified.mp (etale_zpow_id_left_of_isUnit A d hd)).1 a

/-- **Stacks Project, Tag 03RP, clause (4), for `n` invertible in `k`**, with a natural-number
exponent: over an algebraically closed field `k`, every rational point of an abelian variety is
an `n`-th power. -/
theorem exists_pow_eq_of_isUnit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k)) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, b ^ n = a := by
  obtain ⟨b, hb⟩ := exists_zpow_eq_of_isUnit A (n : ℤ) (by simpa using hn) a
  exact ⟨b, by rw [hb, zpow_natCast]⟩

/-- **Stacks Project, Tag 03RP, clause (4), for `n` invertible in `k`, additively**: over an
algebraically closed field `k`, the group `A(k)` of rational points of an abelian variety,
written additively, is `n`-divisible. -/
@[sga "3 VIII 7.11" "special case"]
theorem exists_nsmul_eq_of_isUnit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k)) (a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ∃ b : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), n • b = a := by
  obtain ⟨b, hb⟩ := exists_pow_eq_of_isUnit A n hn (Additive.toMul a)
  exact ⟨Additive.ofMul b, by rw [← ofMul_pow, hb, ofMul_toMul]⟩

/-- **The `n`-divisibility of `A(k)`, for `n` invertible in an algebraically closed `k`,
transported to any additive group `A(k)` surjects onto.** This is the shape in which a
consumer identifying a group with the rational points of an abelian variety uses clause (4) of
Tag 03RP. -/
@[sga "3 VIII 7.11" "special case"]
theorem exists_nsmul_eq_of_surjective_of_isUnit [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℕ) (hn : IsUnit (n : k))
    {P : Type*} [AddCommGroup P] (φ : (𝟙_ (Over (Spec (.of k))) ⟶ A) → P)
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) (hsurj : Function.Surjective φ) (x : P) :
    ∃ y, x = n • y :=
  exists_nsmul_eq_of_surjective A n
    (Etale.iff_flat_and_formallyUnramified.mp
      (etale_zpow_id_left_of_isUnit A n (by simpa using hn))).1
    φ hmul hsurj x

end Stacks.Groupoids

end
