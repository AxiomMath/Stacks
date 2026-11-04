module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel

/-!
# The ideal powers `Iᵏ 𝒪_{Xₘ}` of a cartesian adic tower, and their multiplication

The middle of the second paragraph of the proof of [Stacks, Tag 089A] multiplies the transition
kernels through the ideal powers of a member of the tower high enough up: for `m > n₁ + n₂` the
source uses

  `I^{n₁}𝒪_{Xₘ} × I^{n₂}𝒪_{Xₘ} ⟶ I^{n₁+n₂}𝒪_{Xₘ} ⟶ 𝓕_{n₁+n₂}`.

This file carries the ideal sheaves `Iᵏ 𝒪_{Xₘ}` and the first of those two maps.

`Iᵏ 𝒪_{Xₘ}` is **not** defined as a power of an ideal sheaf. It is the inverse image along
`qₘ : Xₘ ⟶ Sₘ` of the ideal sheaf of the closed subscheme `Spec (A / Iᵏ)` of
`Sₘ = Spec (A / I^{m+1})` — which is what the cartesian squares make it — because that
description is the one every statement about it reduces to: on an affine open of `Xₘ` the
ideal is the extension of an ideal of `A / I^{m+1}` (`Stacks.IdealSheaf.ideal_comap_appLE`),
and the multiplication is then `I^{k₁} · I^{k₂} ⊆ I^{k₁+k₂}` downstairs.

The two members of this family that the tower already names are recovered as
`Stacks.AdicTower.towerIdealPow_one` (`k = 1` is the ideal of `X₀`) and
`Stacks.AdicTower.towerIdealPow_self` (`k = m` at `m = n + 1` is the ideal of `Xₙ`, that is,
the transition kernel).

## Main definitions

* `Stacks.AdicTower.baseIdealPow`: `Iᵏ 𝒪_{Sₘ}`, the ideal sheaf of `Spec (A / Iᵏ)` in `Sₘ`.
* `Stacks.AdicTower.towerIdealPow`: **`Iᵏ 𝒪_{Xₘ}`**, its inverse image on `Xₘ`.

## Main results

* `Stacks.AdicTower.ideal_towerIdealPow`: on an affine open of `Xₘ` the ideal is extended from
  `A / I^{m+1}`.
* `Stacks.AdicTower.ideal_mul_ideal_le_towerIdealPow`: **the multiplication
  `I^{k₁}𝒪_{Xₘ} · I^{k₂}𝒪_{Xₘ} ⊆ I^{k₁+k₂}𝒪_{Xₘ}`.**
* `Stacks.AdicTower.towerIdealPow_one` and `Stacks.AdicTower.towerIdealPow_self`: the ideal of
  `X₀` and the transition kernel are members of the family.
* `Stacks.AdicTower.towerIdealPow_eq_bot`: `I^{m+1}𝒪_{Xₘ} = 0`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AdicTower

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### Ideal powers on the affine base -/

/-- The canonical surjection `A / I ^ (m + 1) → A / I ^ k`, as a morphism of `CommRingCat`. -/
abbrev basePowHom (m k : ℕ) (h : k ≤ m + 1) :
    CommRingCat.of (A ⧸ I ^ (m + 1)) ⟶ CommRingCat.of (A ⧸ I ^ k) :=
  CommRingCat.ofHom (Ideal.Quotient.factorPow I h)

/-- **`Iᵏ 𝒪_{Sₘ}`**: the ideal sheaf of the closed subscheme `Spec (A / Iᵏ)` of the `m`-th adic
thickening `Sₘ = Spec (A / I^{m+1})`. -/
def baseIdealPow (m k : ℕ) (h : k ≤ m + 1) : (adicThickening A I m).IdealSheafData :=
  (Spec.map (basePowHom A I m k h)).ker

/-- The global-sections isomorphism of an affine scheme kills exactly zero. -/
private lemma ΓSpecIso_hom_apply_eq_zero_iff (R : CommRingCat.{u}) (x : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso R).hom.hom x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1

/-- Membership in the ideal of global sections of `Iᵏ 𝒪_{Sₘ}`, read in `A / I ^ (m + 1)`. -/
lemma mem_ker_appTop_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : Γ(Spec R, ⊤)) :
    x ∈ RingHom.ker (Spec.map φ).appTop.hom ↔ (Scheme.ΓSpecIso R).hom.hom x ∈
      RingHom.ker φ.hom := by
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) x
  simp only [CommRingCat.comp_apply] at hn
  simp only [RingHom.mem_ker, ← hn]
  exact (ΓSpecIso_hom_apply_eq_zero_iff _ _).symm

/-- The global ideal of `Iᵏ 𝒪_{Sₘ}` is `Iᵏ` read in `A / I ^ (m + 1)`. -/
lemma ideal_baseIdealPow_top (m k : ℕ) (h : k ≤ m + 1) :
    (baseIdealPow A I m k h).ideal ⟨⊤, isAffineOpen_top _⟩ =
      RingHom.ker (Spec.map (basePowHom A I m k h)).appTop.hom :=
  Scheme.Hom.ker_apply _ _

/-- **The ideal powers on the affine base multiply.** -/
lemma mul_mem_ker_appTop_basePowHom (m k₁ k₂ : ℕ) (h₁ : k₁ ≤ m + 1) (h₂ : k₂ ≤ m + 1)
    (h : k₁ + k₂ ≤ m + 1) (a b : Γ(adicThickening A I m, ⊤))
    (ha : a ∈ RingHom.ker (Spec.map (basePowHom A I m k₁ h₁)).appTop.hom)
    (hb : b ∈ RingHom.ker (Spec.map (basePowHom A I m k₂ h₂)).appTop.hom) :
    a * b ∈ RingHom.ker (Spec.map (basePowHom A I m (k₁ + k₂) h)).appTop.hom := by
  rw [mem_ker_appTop_iff] at ha hb ⊢
  simp only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker] at ha hb ⊢
  have hmem := Ideal.mul_mem_mul ha hb
  rw [← Ideal.map_mul, ← pow_add] at hmem
  rw [map_mul]
  exact hmem

/-- **`I 𝒪_{Sₘ}` is the ideal sheaf of `S₀` in `Sₘ`.** -/
lemma baseIdealPow_one (m : ℕ) (h : 1 ≤ m + 1) :
    baseIdealPow A I m 1 h = (thickeningIncl A I m).ker := by
  rw [thickeningIncl_eq]
  rfl

/-- **`I^{n+1} 𝒪_{S_{n+1}}` is the ideal sheaf of `Sₙ` in `S_{n+1}`.** -/
lemma baseIdealPow_self (n : ℕ) (h : n + 1 ≤ n + 1 + 1) :
    baseIdealPow A I (n + 1) (n + 1) h = (adicThickeningSucc A I n).ker := rfl

/-! ### Ideal powers on the tower -/

variable {A I}
variable {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
  (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

/-- **`Iᵏ 𝒪_{Xₘ}`**: the inverse image along `qₘ : Xₘ ⟶ Sₘ` of the ideal sheaf `Iᵏ 𝒪_{Sₘ}`.
Because the squares of the tower are cartesian this is the ideal sheaf of the closed subscheme
`X_{k-1}` of `Xₘ`. -/
def towerIdealPow (m k : ℕ) (h : k ≤ m + 1) : (Xn m).IdealSheafData :=
  (baseIdealPow A I m k h).comap (q m)

/-- The comparison map on sections from the whole of the affine base `Sₘ` to an affine open of
`Xₘ`, along which the ideal powers of `Xₘ` are extended from `A / I ^ (m + 1)`. -/
abbrev baseAppLEAt (m : ℕ) (U : (Xn m).affineOpens) :
    Γ(adicThickening A I m, ⊤) ⟶ Γ(Xn m, (U : (Xn m).Opens)) :=
  (q m).appLE (⊤ : (adicThickening A I m).Opens) (U : (Xn m).Opens) le_top

/-- **On an affine open of `Xₘ` the ideal `Iᵏ 𝒪_{Xₘ}` is extended from `A / I^{m+1}`.** -/
lemma ideal_towerIdealPow (m k : ℕ) (h : k ≤ m + 1) (U : (Xn m).affineOpens) :
    (towerIdealPow q m k h).ideal U =
      (RingHom.ker (Spec.map (basePowHom A I m k h)).appTop.hom).map
        (baseAppLEAt q m U).hom := by
  refine (Stacks.IdealSheaf.ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ U le_top).trans ?_
  rw [ideal_baseIdealPow_top]

/-- **The multiplication `I^{k₁}𝒪_{Xₘ} · I^{k₂}𝒪_{Xₘ} ⊆ I^{k₁+k₂}𝒪_{Xₘ}`**, on an affine open.
This is the first of the two maps the source composes to multiply the transition kernels. -/
lemma ideal_mul_ideal_le_towerIdealPow (m k₁ k₂ : ℕ) (h₁ : k₁ ≤ m + 1) (h₂ : k₂ ≤ m + 1)
    (h : k₁ + k₂ ≤ m + 1) (U : (Xn m).affineOpens) :
    (towerIdealPow q m k₁ h₁).ideal U * (towerIdealPow q m k₂ h₂).ideal U ≤
      (towerIdealPow q m (k₁ + k₂) h).ideal U := by
  rw [ideal_towerIdealPow q m k₁ h₁ U, ideal_towerIdealPow q m k₂ h₂ U,
    ideal_towerIdealPow q m (k₁ + k₂) h U, ← Ideal.map_mul]
  refine Ideal.map_mono (Ideal.mul_le.mpr fun a ha b hb => ?_)
  exact mul_mem_ker_appTop_basePowHom A I m k₁ k₂ h₁ h₂ h a b ha hb

include hcart in
/-- **`I 𝒪_{Xₘ}` is the ideal sheaf of `X₀` in `Xₘ`.** -/
lemma towerIdealPow_one (m : ℕ) (h : 1 ≤ m + 1) :
    towerIdealPow q m 1 h = (incl t m).ker := by
  rw [towerIdealPow, baseIdealPow_one]
  exact (ker_of_isPullback (isPullback_incl q t hcart m)).symm

include hcart in
/-- **`I^{n+1} 𝒪_{X_{n+1}}` is the ideal sheaf of `Xₙ` in `X_{n+1}`**, that is, the transition
kernel of the tower. -/
lemma towerIdealPow_self (n : ℕ) (h : n + 1 ≤ n + 1 + 1) :
    towerIdealPow q (n + 1) (n + 1) h = (t n).ker := by
  rw [towerIdealPow, baseIdealPow_self]
  exact (ker_transition q t hcart n).symm

/-- **`I^{m+1} 𝒪_{Xₘ}` vanishes**: `Xₘ` lives over `Spec (A / I^{m+1})`. -/
lemma towerIdealPow_eq_bot (m : ℕ) (U : (Xn m).affineOpens) :
    (towerIdealPow q m (m + 1) le_rfl).ideal U = ⊥ := by
  rw [ideal_towerIdealPow q m (m + 1) le_rfl U]
  refine le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
  rw [mem_ker_appTop_iff] at hx
  simp only [CommRingCat.hom_ofHom, Ideal.Quotient.factor_ker] at hx
  rw [Ideal.map_mk_eq_bot_of_le le_rfl, Ideal.mem_bot] at hx
  simp only [Ideal.mem_comap, Ideal.mem_bot]
  rw [(ΓSpecIso_hom_apply_eq_zero_iff _ _).1 hx, map_zero]

end Stacks.AdicTower

end
