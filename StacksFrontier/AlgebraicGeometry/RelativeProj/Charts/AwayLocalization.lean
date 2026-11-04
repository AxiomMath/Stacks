module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Standard affine charts of a degreewise localization of a graded ring

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings and let `g` be a degree-zero
element of `𝒜`. Say that `φ` is a *degreewise localization away from `g`* when the image of `g`
is invertible, every homogeneous element of `ℬ` is the image of one of `𝒜` divided by a power of
that image, and the kernel of `φ` on each homogeneous piece is `g`-power torsion — in other
words when `ℬ n` is the localization of `𝒜 n` away from `g`, for every `n`.

This file proves that such a `φ` localizes the standard affine charts: for `b` homogeneous,
`HomogeneousLocalization.Away ℬ (φ b)` is the localization of
`HomogeneousLocalization.Away 𝒜 b` away from the fraction `g / 1`.

Geometrically this says that the chart `Proj ℬ ⊇ D₊(φ b) ⟶ D₊(b) ⊆ Proj 𝒜` is the inclusion of
the standard open cut out by `g`, which is how one sees that `Proj ℬ ⟶ Proj 𝒜` is the inclusion
of the part of `Proj 𝒜` lying over the nonvanishing locus of `g`. Nothing in this file mentions
schemes.

## Main definitions

* `Stacks.GradedLocalization.IsAwayDegreewise` is the hypothesis described above.
* `Stacks.GradedLocalization.chartElem` is the fraction `g / 1` in
  `HomogeneousLocalization.Away 𝒜 b`.

## Main results

* `Stacks.GradedLocalization.isUnit_chartElem`: the fraction `u / 1` of a degree-zero unit `u` is
  a unit.
* `Stacks.GradedLocalization.IsAwayDegreewise.isLocalization_awayMap`: the chart of `ℬ` at `φ b`
  is the localization of the chart of `𝒜` at `b` away from `g / 1`.

## Implementation notes

`IsAwayDegreewise` is stated elementwise rather than as a conjunction of `IsLocalizedModule`
hypotheses on the homogeneous pieces. Those pieces are carriers of a `SetLike`, so putting an
`IsLocalizedModule` on each would need a module structure on every `𝒜 n` over the degree-zero
part together with a linear map between them; the three elementwise statements are what the
proofs use and what a caller can supply directly from a localization hypothesis on sections.

`isUnit_chartElem` needs the inverse of a degree-zero unit to be itself of degree zero. That is
proved by applying the ring homomorphism `GradedRing.projZeroRingHom'` to the equation `x * v = 1`:
it fixes `x`, so the degree-zero component of `v` is already a right inverse.

The three fields of `IsLocalization` are each a computation with `Localization.mk` after
`HomogeneousLocalization.val_injective`, reduced to an equation in `𝒜` by
`Localization.r_iff_exists`. For `exists_of_eq` the element to which the torsion hypothesis is
applied is `b ^ j * (b ^ m * a - b ^ n * a')`, homogeneous because the two products have the same
degree, where `(φ b) ^ j` is the witness that the two images agree.
-/

@[expose] public section

open HomogeneousLocalization

universe u

namespace Stacks.GradedLocalization

variable {A B : Type u} {σ τ : Type*}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

variable {φ : 𝒜 →+*ᵍ ℬ} {g b : A} {d : ℕ}

/-- A homomorphism of nonnegatively graded rings which is, in each degree, the localization away
from a degree-zero element `g` of the source. -/
public structure IsAwayDegreewise (φ : 𝒜 →+*ᵍ ℬ) (g : A) : Prop where
  /-- The image of `g` is invertible. -/
  isUnit_map : IsUnit (φ g)
  /-- Every homogeneous element of `ℬ` becomes the image of a homogeneous element of `𝒜` of the
  same degree after multiplication by a power of the image of `g`. -/
  surj (n : ℕ) (y : B) (hy : y ∈ ℬ n) : ∃ (k : ℕ) (x : A), x ∈ 𝒜 n ∧ φ x = φ g ^ k * y
  /-- A homogeneous element of `𝒜` in the kernel is killed by a power of `g`. -/
  torsion (n : ℕ) (x : A) (hx : x ∈ 𝒜 n) (h : φ x = 0) : ∃ k : ℕ, g ^ k * x = 0

/-- The fraction `g / 1` in the standard affine chart of `Proj 𝒜` at a homogeneous `b`, for `g`
of degree zero. -/
public noncomputable def chartElem (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d) : Away 𝒜 b :=
  Away.mk 𝒜 hb 0 g (by simpa using hg)

/-- The underlying fraction of `chartElem` is `g / 1`. -/
public theorem val_chartElem (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d) :
    (chartElem hg hb).val = Localization.mk g 1 := by
  rw [chartElem, Away.val_mk]
  congr 1
  simp

/-- Taking the fraction `g / 1` commutes with a homomorphism of graded rings. -/
public theorem map_chartElem (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d) :
    Away.map φ b (chartElem hg hb) = chartElem (φ.map_mem hg) (φ.map_mem hb) := by
  rw [chartElem, Away.map_mk]
  rfl

/-- Two degree-zero fractions with denominator `1` whose numerators multiply to `1` are inverse
to each other. -/
public theorem chartElem_mul_chartElem {x y : A} (hb : b ∈ 𝒜 d) (hx : x ∈ 𝒜 0) (hy : y ∈ 𝒜 0)
    (hxy : x * y = 1) : chartElem hx hb * chartElem hy hb = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, chartElem, chartElem, Away.val_mk, Away.val_mk, Localization.mk_mul, hxy, val_one]
  simp

/-- **The fraction `u / 1` of a degree-zero unit is a unit.** The inverse of a degree-zero unit
is again of degree zero, because `GradedRing.projZeroRingHom'` is a ring homomorphism fixing it. -/
public theorem isUnit_chartElem (hb : b ∈ 𝒜 d) {x : A} (hx : x ∈ 𝒜 0) (hu : IsUnit x) :
    IsUnit (chartElem hx hb) := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv0 : (GradedRing.projZeroRingHom' 𝒜 v : A) ∈ 𝒜 0 := SetLike.coe_mem _
  have hx' : GradedRing.projZeroRingHom' 𝒜 x = ⟨x, hx⟩ :=
    GradedRing.projZeroRingHom'_apply_coe 𝒜 ⟨x, hx⟩
  have hprod : x * (GradedRing.projZeroRingHom' 𝒜 v : A) = 1 := by
    have := congrArg (GradedRing.projZeroRingHom' 𝒜) hv
    rw [map_mul, map_one, hx'] at this
    exact congrArg Subtype.val this
  exact isUnit_iff_exists_inv.mpr ⟨_, chartElem_mul_chartElem hb hx hv0 hprod⟩

namespace IsAwayDegreewise

/-- Powers of `g / 1` become units in the chart of `ℬ`. -/
private theorem isUnit_awayMap_powers (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d)
    (y : Away 𝒜 b)
    (hy : y ∈ Submonoid.powers (chartElem hg hb)) : IsUnit (Away.map φ b y) := by
  obtain ⟨k, rfl⟩ := hy
  rw [map_pow, map_chartElem]
  exact (isUnit_chartElem (φ.map_mem hb) (φ.map_mem hg) h.isUnit_map).pow k

/-- Every element of the chart of `ℬ` is a fraction over the chart of `𝒜` with denominator a
power of `g / 1`. -/
private theorem awayMap_surj (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d)
    (z : Away ℬ (φ b)) :
    ∃ x : Away 𝒜 b × Submonoid.powers (chartElem hg hb),
      z * Away.map φ b x.2 = Away.map φ b x.1 := by
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ (φ.map_mem hb) z
  obtain ⟨k, x, hx, hxy⟩ := h.surj (n • d) y hy
  refine ⟨⟨Away.mk 𝒜 hb n x hx, ⟨chartElem hg hb ^ k, k, rfl⟩⟩, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.map_mk, Away.val_mk, Away.val_mk, map_pow, map_chartElem, val_pow,
    val_chartElem, Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp [hxy]; ring⟩

/-- Two elements of the chart of `𝒜` with the same image agree after multiplication by a power
of `g / 1`. -/
private theorem awayMap_exists_of_eq (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0) (hb : b ∈ 𝒜 d)
    {x y : Away 𝒜 b} (hxy : Away.map φ b x = Away.map φ b y) :
    ∃ c : Submonoid.powers (chartElem hg hb), (c : Away 𝒜 b) * x = (c : Away 𝒜 b) * y := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hb x
  obtain ⟨m, a', ha', rfl⟩ := Away.mk_surjective 𝒜 hb y
  rw [Away.map_mk, Away.map_mk] at hxy
  replace hxy := congrArg HomogeneousLocalization.val hxy
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := hxy
  have hwmem : b ^ j * (b ^ m * a - b ^ n * a') ∈ 𝒜 (j • d + (m • d + n • d)) := by
    refine SetLike.mul_mem_graded (SetLike.pow_mem_graded j hb) (sub_mem ?_ ?_)
    · exact SetLike.mul_mem_graded (SetLike.pow_mem_graded m hb) ha
    · have hswap : n • d + m • d = m • d + n • d := by ring
      exact hswap ▸ SetLike.mul_mem_graded (SetLike.pow_mem_graded n hb) ha'
  have hzero : φ (b ^ j * (b ^ m * a - b ^ n * a')) = 0 := by
    have hsplit : φ (b ^ j * (b ^ m * a - b ^ n * a')) =
        φ b ^ j * (φ b ^ m * φ a) - φ b ^ j * (φ b ^ n * φ a') := by
      simp only [map_mul, map_sub, map_pow]; ring
    rw [hsplit, hj, sub_self]
  obtain ⟨k, hk⟩ := h.torsion _ _ hwmem hzero
  refine ⟨⟨chartElem hg hb ^ k, k, rfl⟩, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_mul, val_pow, val_chartElem, Away.val_mk, Away.val_mk, Localization.mk_pow,
    Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨⟨b ^ j, j, rfl⟩, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  have expand : g ^ k * (b ^ j * (b ^ m * a - b ^ n * a')) =
      b ^ j * (b ^ m * (g ^ k * a)) - b ^ j * (b ^ n * (g ^ k * a')) := by ring
  rw [expand, sub_eq_zero] at hk
  simpa [mul_comm, mul_assoc, mul_left_comm] using hk

/-- **The standard affine charts of a degreewise localization are localizations.** If `φ` is, in
each degree, the localization of `𝒜` away from the degree-zero element `g`, then for `b`
homogeneous the chart `Away ℬ (φ b)` is the localization of the chart `Away 𝒜 b` away from the
fraction `g / 1`. -/
public theorem isLocalization_awayMap (h : IsAwayDegreewise φ g) (hg : g ∈ 𝒜 0)
    (hb : b ∈ 𝒜 d) :
    letI := (Away.map φ b).toAlgebra
    IsLocalization.Away (chartElem hg hb) (Away ℬ (φ b)) := by
  let := (Away.map φ b).toAlgebra
  constructor
  constructor
  · exact fun y => isUnit_awayMap_powers h hg hb y y.2
  · exact awayMap_surj h hg hb
  · exact fun hxy => awayMap_exists_of_eq h hg hb hxy

end IsAwayDegreewise

end Stacks.GradedLocalization

end
