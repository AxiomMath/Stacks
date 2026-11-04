module

public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree

/-!
# Localizing at a homogeneous element of degree `d`, read on the `d`-th Veronese subring

Let `S = ⨁_{n ≥ 0} S_n` be a graded ring and let `a ∈ S_d`. In the `d`-th Veronese subring
`S⁽ᵈ⁾ ⊆ S`, whose degree-`n` component is `S_{nd}` (`Stacks.Veronese.veroneseGrading`), the
element `a` is homogeneous of degree **one**. This file proves that the degree-zero localizations
agree:

  `S₍a₎ = HomogeneousLocalization.Away S a ≃+* HomogeneousLocalization.Away S⁽ᵈ⁾ a`,

by the identity on fractions `x / aⁿ ↦ x / aⁿ`. The point is that nothing has to move: a
degree-zero element of `S[1/a]` is a fraction `x / aⁿ` whose numerator is homogeneous of degree
`n · d`, so the numerator already lies in the Veronese subring, where it is homogeneous of Veronese
degree `n`. The two rings have the same fractions, written with the same symbols; only the degree
in which the numerator is counted changes.

This is the bridge between the two `Away` rings that lets a chart of `Proj` at an element of
arbitrary degree `d` be computed by the degree-**one** theory applied to the Veronese subring --
equivalently, for a graded section ring, by the degree-one theory applied to the `d`-th tensor
power of the invertible sheaf.

Note the distinction from `Stacks.Veronese.veroneseAwayEquiv` of
`StacksFrontier/RingTheory/GradedAlgebra/VeroneseGrading.lean`, which compares `(S⁽ᵈ⁾)₍f ᵈ₎` with
`S₍f₎` for `f` of *arbitrary* degree `e`: there the element passed to the Veronese side is `f ^ d`,
of Veronese degree `e`. Here the element passed to the Veronese side is `a` itself, of Veronese
degree one, which is what the degree-one theory consumes; the two statements have the same source
ring `S₍a₎` but different targets, and neither follows from the other by substitution.

## Main definitions

* `Stacks.Veronese.veroneseOfDegree` is `a` viewed as an element of `S⁽ᵈ⁾`, homogeneous of
  Veronese degree one.
* `Stacks.Veronese.veroneseAwayNumerator` is the family of additive maps that reads a numerator of
  degree `n · d` as a fraction over `aⁿ` on the Veronese side; it is the input to the lift of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DegreeZeroLocalizationArbitraryDegree.lean`.
* `Stacks.Veronese.veroneseAwayDegreeOneHom` is the induced ring map, and
  `Stacks.Veronese.veroneseAwayDegreeOneEquiv` the ring isomorphism.

## Main results

* `Stacks.Veronese.veroneseAwayDegreeOneHom_mk`: **the comparison is the identity on fractions**,
  `x / aⁿ ↦ x / aⁿ`.
* `Stacks.Veronese.veroneseAwayDegreeOneHom_bijective`: **the comparison is bijective.**

## Implementation notes

The family of numerator maps has to be additive on all of `S`, not only on a homogeneous
component, so it is defined using the homogeneous projection `DirectSum.decompositionProj` of
`VeroneseGrading.lean`; `Stacks.Veronese.veroneseAwayNumerator_apply_of_mem` then says that on a
numerator of the expected degree the projection does nothing, and every proof below goes through
that lemma rather than through the definition.

The `Away.mk` calculus the comparison needs -- addition and multiplication of fractions with the
denominators `aⁿ`, cancelling a power of `a`, and the vanishing criterion -- is proved once in the
`AwayFractions` section for an arbitrary graded ring and an arbitrary degree, since none of those
facts depends on the degree of the element; each goes through `HomogeneousLocalization.ext_iff_val`
and the corresponding fact about `Localization.mk`.

`0 < d` is never assumed. The grading of the Veronese subring enters only as the typeclass
hypothesis `[GradedRing (veroneseGrading 𝒜 d)]`, following the convention of
`VeroneseGrading.lean`; positivity of `d` is what makes that hypothesis satisfiable
(`Stacks.Veronese.veroneseGradingGradedRing`), and it is the consumer's business to supply it.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.Veronese

open DirectSum

universe u v

/-! ### The `Away.mk` calculus -/

section AwayFractions

variable {B : Type u} {τ : Type v} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ] {b : B} {e : ℕ}

/-- Two fractions with the same numerator and the same denominator are equal: the homogeneity
witnesses are proofs, so they do not enter. -/
public theorem awayMk_congr (hb : b ∈ ℬ e) (n : ℕ) {u v : B} (hu : u ∈ ℬ (n • e))
    (hv : v ∈ ℬ (n • e)) (h : u = v) :
    HomogeneousLocalization.Away.mk ℬ hb n u hu =
      HomogeneousLocalization.Away.mk ℬ hb n v hv := by
  subst h
  rfl

/-- A fraction with numerator `0` vanishes. -/
public theorem awayMk_zero (hb : b ∈ ℬ e) (n : ℕ) (hu : (0 : B) ∈ ℬ (n • e)) :
    HomogeneousLocalization.Away.mk ℬ hb n 0 hu = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_zero]

/-- The fraction `1 / b ^ 0` is the unit. -/
private theorem awayMk_one (hb : b ∈ ℬ e) (hu : (1 : B) ∈ ℬ (0 • e)) :
    HomogeneousLocalization.Away.mk ℬ hb 0 1 hu = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one,
    show (⟨b ^ 0, by exact ⟨0, rfl⟩⟩ : Submonoid.powers b) = 1 from Subtype.ext (pow_zero b),
    Localization.mk_one]

/-- Fractions with a common denominator add by adding numerators. -/
public theorem awayMk_add (hb : b ∈ ℬ e) (n : ℕ) {u v : B} (hu : u ∈ ℬ (n • e))
    (hv : v ∈ ℬ (n • e)) (huv : u + v ∈ ℬ (n • e)) :
    HomogeneousLocalization.Away.mk ℬ hb n u hu +
        HomogeneousLocalization.Away.mk ℬ hb n v hv =
      HomogeneousLocalization.Away.mk ℬ hb n (u + v) huv := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.add_mk_self]

/-- Fractions multiply by multiplying numerators and adding the exponents of the denominators. -/
private theorem awayMk_mul (hb : b ∈ ℬ e) (n m : ℕ) {u v : B} (hu : u ∈ ℬ (n • e))
    (hv : v ∈ ℬ (m • e)) (huv : u * v ∈ ℬ ((n + m) • e)) :
    HomogeneousLocalization.Away.mk ℬ hb n u hu *
        HomogeneousLocalization.Away.mk ℬ hb m v hv =
      HomogeneousLocalization.Away.mk ℬ hb (n + m) (u * v) huv := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add b n m).symm

/-- Multiplying numerator and denominator by `b ^ k` leaves a fraction unchanged. -/
private theorem awayMk_pow_mul (hb : b ∈ ℬ e) (n k : ℕ) {u : B} (hu : u ∈ ℬ (n • e))
    (hku : b ^ k * u ∈ ℬ ((n + k) • e)) :
    HomogeneousLocalization.Away.mk ℬ hb (n + k) (b ^ k * u) hku =
      HomogeneousLocalization.Away.mk ℬ hb n u hu := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  rw [pow_add]
  ring

/-- **A fraction vanishes exactly when a power of the denominator kills its numerator.** -/
private theorem awayMk_eq_zero_iff (hb : b ∈ ℬ e) (n : ℕ) {u : B} (hu : u ∈ ℬ (n • e)) :
    HomogeneousLocalization.Away.mk ℬ hb n u hu = 0 ↔ ∃ k : ℕ, b ^ k * u = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero, ← Localization.mk_zero (1 : Submonoid.powers b),
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨⟨c, k, rfl⟩, hc⟩
    exact ⟨k, by simpa using hc⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨b ^ k, ⟨k, rfl⟩⟩, by simpa using hk⟩

end AwayFractions

/-! ### The comparison -/

section Comparison

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) [GradedRing (veroneseGrading 𝒜 d)] {a : A}

/-- The homogeneous projection lands in its own degree. -/
public theorem decompositionProj_mem (i : ℕ) (x : A) : decompositionProj 𝒜 i x ∈ 𝒜 i := by
  rw [decompositionProj_apply]
  exact SetLike.coe_mem _

omit [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)] in
/-- Membership in the Veronese grading at the degree `n • 1` in which
`HomogeneousLocalization.Away.mk` states it. -/
public theorem mem_veroneseGrading_nsmul_one {n : ℕ} {y : veroneseSubring 𝒜 d}
    (hy : (y : A) ∈ 𝒜 (n * d)) : y ∈ veroneseGrading 𝒜 d (n • 1) := by
  rw [mem_veroneseGrading]
  simpa [smul_eq_mul] using hy

omit [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)] in
/-- The underlying element of a numerator homogeneous of Veronese degree `n • 1` is homogeneous of
degree `n * d`. -/
private theorem coe_mem_of_mem_veroneseGrading_nsmul_one {n : ℕ} {y : veroneseSubring 𝒜 d}
    (hy : y ∈ veroneseGrading 𝒜 d (n • 1)) : (y : A) ∈ 𝒜 (n * d) := by
  rw [mem_veroneseGrading] at hy
  simpa [smul_eq_mul] using hy

/-- **`a` as an element of the `d`-th Veronese subring**, where it is homogeneous of degree
one. -/
public def veroneseOfDegree (ha : a ∈ 𝒜 d) : veroneseSubring 𝒜 d :=
  ⟨a, mem_veroneseSubring_of_mem 𝒜 (n := 1) (by simpa using ha)⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)] in
/-- The underlying element of `veroneseOfDegree 𝒜 d ha` is `a`. -/
@[simp]
public theorem coe_veroneseOfDegree (ha : a ∈ 𝒜 d) :
    ((veroneseOfDegree 𝒜 d ha : veroneseSubring 𝒜 d) : A) = a :=
  rfl

omit [GradedRing 𝒜] [GradedRing (veroneseGrading 𝒜 d)] in
/-- `a` is homogeneous of Veronese degree one. -/
public theorem veroneseOfDegree_mem (ha : a ∈ 𝒜 d) :
    veroneseOfDegree 𝒜 d ha ∈ veroneseGrading 𝒜 d 1 := by
  rw [mem_veroneseGrading]
  simpa using ha

/-- The homogeneous projection onto degree `n * d`, as a map into the Veronese subring. -/
public def veroneseProj (n : ℕ) : A →+ veroneseSubring 𝒜 d where
  toFun x := ⟨decompositionProj 𝒜 (n * d) x, mem_veroneseSubring_of_mem 𝒜
    (decompositionProj_mem 𝒜 (n * d) x)⟩
  map_zero' := Subtype.ext (map_zero (decompositionProj 𝒜 (n * d)))
  map_add' x y := Subtype.ext (map_add (decompositionProj 𝒜 (n * d)) x y)

omit [GradedRing (veroneseGrading 𝒜 d)] in
private theorem coe_veroneseProj (n : ℕ) (x : A) :
    ((veroneseProj 𝒜 d n x : veroneseSubring 𝒜 d) : A) = decompositionProj 𝒜 (n * d) x :=
  rfl

omit [GradedRing (veroneseGrading 𝒜 d)] in
/-- The projection onto degree `n * d` lands in degree `n * d`. -/
public theorem coe_veroneseProj_mem (n : ℕ) (x : A) :
    ((veroneseProj 𝒜 d n x : veroneseSubring 𝒜 d) : A) ∈ 𝒜 (n * d) :=
  decompositionProj_mem 𝒜 (n * d) x

omit [GradedRing (veroneseGrading 𝒜 d)] in
private theorem veroneseProj_of_mem {n : ℕ} {x : A} (hx : x ∈ 𝒜 (n * d)) :
    veroneseProj 𝒜 d n x = ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ :=
  Subtype.ext (decompositionProj_of_mem_same 𝒜 hx)

/-- **The numerator family**: a numerator of degree `n * d` is read as the fraction over `aⁿ` on
the Veronese side, where it is homogeneous of Veronese degree `n`. It is defined on all of `S`
through the homogeneous projection, so that it is additive. -/
public def veroneseAwayNumerator (ha : a ∈ 𝒜 d) (n : ℕ) :
    A →+ HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (veroneseOfDegree 𝒜 d ha) where
  toFun x := HomogeneousLocalization.Away.mk (veroneseGrading 𝒜 d)
    (veroneseOfDegree_mem 𝒜 d ha) n (veroneseProj 𝒜 d n x)
    (mem_veroneseGrading_nsmul_one 𝒜 d (coe_veroneseProj_mem 𝒜 d n x))
  map_zero' :=
    (awayMk_congr (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n _ (zero_mem _)
      (map_zero (veroneseProj 𝒜 d n))).trans
      (awayMk_zero (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n (zero_mem _))
  map_add' x y :=
    ((awayMk_congr (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n _
      (add_mem (mem_veroneseGrading_nsmul_one 𝒜 d (coe_veroneseProj_mem 𝒜 d n x))
        (mem_veroneseGrading_nsmul_one 𝒜 d (coe_veroneseProj_mem 𝒜 d n y)))
      (map_add (veroneseProj 𝒜 d n) x y)).trans
      (awayMk_add (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n _ _ _).symm)

/-- On a numerator of the expected degree the projection does nothing: the numerator family is the
fraction `x / aⁿ`. Every statement below is proved through this lemma rather than through the
definition. -/
public theorem veroneseAwayNumerator_apply_of_mem (ha : a ∈ 𝒜 d) (n : ℕ) {x : A}
    (hx : x ∈ 𝒜 (n * d))
    (hy : (⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ : veroneseSubring 𝒜 d) ∈
      veroneseGrading 𝒜 d (n • 1)) :
    veroneseAwayNumerator 𝒜 d ha n x =
      HomogeneousLocalization.Away.mk (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n
        ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ hy :=
  awayMk_congr (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n _ hy
    (veroneseProj_of_mem 𝒜 d hx)

/-- The numerator family at a numerator of the expected degree, with the Veronese degree of the
numerator derived from its degree in `S`. -/
private theorem veroneseAwayNumerator_eq_mk (ha : a ∈ 𝒜 d) (n : ℕ) {x : A} (hx : x ∈ 𝒜 (n * d)) :
    veroneseAwayNumerator 𝒜 d ha n x =
      HomogeneousLocalization.Away.mk (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n
        ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ (mem_veroneseGrading_nsmul_one 𝒜 d hx) :=
  veroneseAwayNumerator_apply_of_mem 𝒜 d ha n hx _

/-- The numerator family is compatible with multiplying numerator and denominator by `a`. -/
public theorem veroneseAwayNumerator_pow_mul (ha : a ∈ 𝒜 d) (n k : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n * d)) :
    veroneseAwayNumerator 𝒜 d ha (n + k) (a ^ k * x) = veroneseAwayNumerator 𝒜 d ha n x := by
  have hax : a ^ k * x ∈ 𝒜 ((n + k) * d) :=
    SetLike.mul_mem_graded_mul (Nat.add_comm k n) (SetLike.pow_mem_graded k ha) hx
  rw [veroneseAwayNumerator_eq_mk 𝒜 d ha _ hax, veroneseAwayNumerator_eq_mk 𝒜 d ha n hx]
  exact awayMk_pow_mul (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n k
    (u := ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩) (mem_veroneseGrading_nsmul_one 𝒜 d hx)
    (mem_veroneseGrading_nsmul_one 𝒜 d hax)

/-- The numerator family sends the unit to the unit. -/
public theorem veroneseAwayNumerator_one (ha : a ∈ 𝒜 d) :
    veroneseAwayNumerator 𝒜 d ha 0 1 = 1 := by
  have h1 : (1 : A) ∈ 𝒜 (0 * d) := by simpa using SetLike.one_mem_graded 𝒜
  rw [veroneseAwayNumerator_eq_mk 𝒜 d ha 0 h1]
  exact awayMk_one (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) _

/-- The numerator family is multiplicative on numerators. -/
public theorem veroneseAwayNumerator_mul (ha : a ∈ 𝒜 d) (n m : ℕ) (x y : A)
    (hx : x ∈ 𝒜 (n * d)) (hy : y ∈ 𝒜 (m * d)) :
    veroneseAwayNumerator 𝒜 d ha (n + m) (x * y) =
      veroneseAwayNumerator 𝒜 d ha n x * veroneseAwayNumerator 𝒜 d ha m y := by
  have hxy : x * y ∈ 𝒜 ((n + m) * d) := SetLike.mul_mem_graded_mul rfl hx hy
  rw [veroneseAwayNumerator_eq_mk 𝒜 d ha _ hxy, veroneseAwayNumerator_eq_mk 𝒜 d ha n hx,
    veroneseAwayNumerator_eq_mk 𝒜 d ha m hy]
  exact (awayMk_mul (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n m
    (u := ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩) (v := ⟨y, mem_veroneseSubring_of_mem 𝒜 hy⟩)
    (mem_veroneseGrading_nsmul_one 𝒜 d hx) (mem_veroneseGrading_nsmul_one 𝒜 d hy)
    (mem_veroneseGrading_nsmul_one 𝒜 d hxy)).symm

/-- **The comparison ring map** `S₍a₎ →+* (S⁽ᵈ⁾)₍a₎`, for `a` homogeneous of degree `d` in `S` and
hence of degree one in `S⁽ᵈ⁾`. -/
public def veroneseAwayDegreeOneHom (ha : a ∈ 𝒜 d) :
    HomogeneousLocalization.Away 𝒜 a →+*
      HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (veroneseOfDegree 𝒜 d ha) :=
  Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree 𝒜 ha
    (veroneseAwayNumerator 𝒜 d ha)
    (fun n k x hx => veroneseAwayNumerator_pow_mul 𝒜 d ha n k x hx)
    (veroneseAwayNumerator_one 𝒜 d ha)
    (fun n m x y hx hy => veroneseAwayNumerator_mul 𝒜 d ha n m x y hx hy)

/-- **The comparison is the identity on fractions**: `x / aⁿ ↦ x / aⁿ`. -/
public theorem veroneseAwayDegreeOneHom_mk (ha : a ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n * d))
    (hy : (⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ : veroneseSubring 𝒜 d) ∈
      veroneseGrading 𝒜 d (n • 1))
    (z : HomogeneousLocalization.Away 𝒜 a)
    (hz : HomogeneousLocalization.val z =
      Localization.mk x (⟨a ^ n, by exact ⟨n, rfl⟩⟩ : Submonoid.powers a)) :
    veroneseAwayDegreeOneHom 𝒜 d ha z =
      HomogeneousLocalization.Away.mk (veroneseGrading 𝒜 d) (veroneseOfDegree_mem 𝒜 d ha) n
        ⟨x, mem_veroneseSubring_of_mem 𝒜 hx⟩ hy :=
  (Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_fraction 𝒜 ha
    (veroneseAwayNumerator 𝒜 d ha) _ _ _ z n x hx hz).trans
    (veroneseAwayNumerator_apply_of_mem 𝒜 d ha n hx hy)

/-- **The comparison is bijective.** Both rings are the fractions `x / aⁿ` with numerator
homogeneous of degree `n * d`, written with the same symbols. -/
public theorem veroneseAwayDegreeOneHom_bijective (ha : a ∈ 𝒜 d) :
    Function.Bijective (veroneseAwayDegreeOneHom 𝒜 d ha) := by
  constructor
  · refine Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective 𝒜 ha _ _ _ _
      (fun n x hx hzero => ?_)
    rw [veroneseAwayNumerator_eq_mk 𝒜 d ha n hx] at hzero
    obtain ⟨k, hk⟩ := (awayMk_eq_zero_iff (veroneseGrading 𝒜 d)
      (veroneseOfDegree_mem 𝒜 d ha) n _).mp hzero
    exact ⟨k, by simpa using congrArg (fun y : veroneseSubring 𝒜 d => (y : A)) hk⟩
  · refine Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_surjective 𝒜 ha _ _ _ _
      (fun y => ?_)
    obtain ⟨n, c, hc, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (veroneseGrading 𝒜 d)
      (veroneseOfDegree_mem 𝒜 d ha) y
    refine ⟨n, (c : A), coe_mem_of_mem_veroneseGrading_nsmul_one 𝒜 d hc, ?_⟩
    rw [veroneseAwayNumerator_eq_mk 𝒜 d ha n (coe_mem_of_mem_veroneseGrading_nsmul_one 𝒜 d hc)]

/-- **Localizing at a homogeneous element of degree `d` is the same as localizing the `d`-th
Veronese subring, where that element has degree one**, as a ring isomorphism. -/
public def veroneseAwayDegreeOneEquiv (ha : a ∈ 𝒜 d) :
    HomogeneousLocalization.Away 𝒜 a ≃+*
      HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (veroneseOfDegree 𝒜 d ha) :=
  RingEquiv.ofBijective (veroneseAwayDegreeOneHom 𝒜 d ha)
    (veroneseAwayDegreeOneHom_bijective 𝒜 d ha)

/-- The ring isomorphism `veroneseAwayDegreeOneEquiv` acts as the comparison map. -/
@[simp]
public theorem veroneseAwayDegreeOneEquiv_apply (ha : a ∈ 𝒜 d)
    (z : HomogeneousLocalization.Away 𝒜 a) :
    veroneseAwayDegreeOneEquiv 𝒜 d ha z = veroneseAwayDegreeOneHom 𝒜 d ha z :=
  rfl

end Comparison

end Stacks.Veronese

end
