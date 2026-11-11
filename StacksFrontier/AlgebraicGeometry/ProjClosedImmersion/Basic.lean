module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MapBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Proj` of a graded quotient is a closed subscheme

Let `f : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings with `ℬ₊ ≤ 𝒜₊.map f`, so that
`AlgebraicGeometry.Proj.map f` is defined, and suppose that `𝒜 d ⟶ ℬ d` is surjective for all
`d ≫ 0`. Then `Proj.map f : Proj ℬ ⟶ Proj 𝒜` is a closed immersion.

The argument is the one of the source, and it is entirely local. Being a closed immersion is
Zariski-local at the target, and the standard affine charts `Spec (Away 𝒜 s)` cover `Proj 𝒜`, so
it suffices to see that each chart comparison

`Spec (Away ℬ (f s)) ⟶ Spec (Away 𝒜 s)`

is a closed immersion, which it is because `Away 𝒜 s ⟶ Away ℬ (f s)` is surjective: an element of
`Away ℬ (f s)` is a fraction `b / (f s) ^ n` whose numerator is homogeneous of degree `n • deg s`,
and multiplying numerator and denominator by a further power of `f s` represents it with a
numerator of arbitrarily large degree, where `f` is surjective by hypothesis.

## Main definitions

* `Stacks.Proj.SurjectiveInLargeDegrees` is the hypothesis `𝒜 d ⟶ ℬ d` surjective for `d ≫ 0`.

## Main results

* `GradedRingHom.exists_mem_of_surjective`: a surjective homomorphism of graded rings is
  surjective in every single degree.
* `AlgebraicGeometry.Proj.surjective_awayMap`: the chart comparison
  `Away 𝒜 s ⟶ Away ℬ (f s)` is surjective at every homogeneous `s` of positive degree.
* `AlgebraicGeometry.Proj.isClosedImmersion_map`: **`Proj.map f` is a closed immersion**, given
  that every chart comparison is one.
* `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjectiveInLargeDegrees` and
  `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective`: the two forms in which the
  hypothesis is met in practice.

## Implementation notes

`Stacks.Proj.SurjectiveInLargeDegrees` is stated as surjectivity of `𝒜 d → ℬ d` for `d` beyond a
bound rather than as `Function.Surjective f`, because that is the hypothesis of the source and it
is strictly weaker: for the graded ring `k[x, y]` with `deg x = 1`, `deg y = 2` and `ℬ = k[y]` it
holds while `f` is not surjective. It does *not* imply `ℬ₊ ≤ 𝒜₊.map f` — that needs surjectivity
in *every* positive degree — so `AlgebraicGeometry.Proj.map`'s side condition stays an explicit
hypothesis, and it is discharged separately for a genuinely surjective `f`.

No `@[stacks]` attribute is attached. Tag 01N0 has three parts; parts (1) and (2) are what is
proved here, part (1) being `AlgebraicGeometry.Proj.map`'s own side condition `ℬ₊ ≤ 𝒜₊.map f`
(`U(ψ) = Y`) and part (2) the closed immersion, both for Mathlib's `AlgebraicGeometry.Proj.map`.
The tag itself, under its own hypothesis and with part (3) on the comparison maps
`r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)`, is carried in
`StacksFrontier/AlgebraicGeometry/RelativeProjChain/EventualSurjective.lean`,
`StacksFrontier/AlgebraicGeometry/ProjTwistEpi/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/ProjTwistCompare/NotIsoExample.lean`.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization Graded

namespace GradedRingHom

variable {ι A B σ τ : Type*} [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **A surjective homomorphism of graded rings is surjective in every degree.** A preimage of a
homogeneous element of degree `i` is given by the degree-`i` component of any preimage, because a
graded ring homomorphism commutes with the homogeneous decomposition. -/
theorem exists_mem_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) {i : ι} {b : B}
    (hb : b ∈ ℬ i) : ∃ a ∈ 𝒜 i, f a = b := by
  obtain ⟨x, rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 x i, Subtype.prop _, ?_⟩
  rw [f.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hb]

end GradedRingHom

namespace Stacks.Proj

variable {A B σ τ : Type*} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The hypothesis of Stacks tag 01N0**: the homomorphism `𝒜 d ⟶ ℬ d` of degree-`d` parts is
surjective for every sufficiently large `d`. -/
@[ega "II 3.6.1" "special case"]
def SurjectiveInLargeDegrees (f : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∃ D : ℕ, ∀ d, D ≤ d → ∀ b ∈ ℬ d, ∃ a ∈ 𝒜 d, f a = b

/-- A surjective homomorphism of graded rings is in particular surjective in large degrees. -/
theorem SurjectiveInLargeDegrees.of_surjective {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) :
    SurjectiveInLargeDegrees f :=
  ⟨0, fun _ _ _ hb ↦ f.exists_mem_of_surjective hf hb⟩

end Stacks.Proj

namespace AlgebraicGeometry.Proj

open Stacks.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ}

/-- Raising the exponent of the denominator of a homogeneous fraction, by multiplying the
numerator by the same power. This is what lets an element of `Away ℬ t` be represented with a
numerator of arbitrarily large degree. -/
private theorem awayMk_mul_pow {d : ℕ} {t : B} (ht : t ∈ ℬ d) (n m : ℕ) {b : B}
    (hb : b ∈ ℬ (n • d)) (hb' : b * t ^ m ∈ ℬ ((n + m) • d)) :
    Away.mk ℬ ht (n + m) (b * t ^ m) hb' = Away.mk ℬ ht n b hb := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff]
  exact Localization.r_iff_exists.mpr ⟨1, by simp [pow_add]; ring⟩

/-- **The chart comparison of `Proj.map f` is surjective on rings.** For `s` homogeneous of
positive degree, `Away 𝒜 s ⟶ Away ℬ (f s)` is surjective as soon as `f` is surjective in large
degrees: an element of the target is `b / (f s) ^ n` with `b` homogeneous of degree `n • deg s`,
and replacing it by `b (f s) ^ D / (f s) ^ (n + D)` puts the degree of the numerator past the
bound, since `deg s > 0`. -/
theorem surjective_awayMap (f : 𝒜 →+*ᵍ ℬ) (hf : SurjectiveInLargeDegrees f) {i : ℕ} (hi : 0 < i)
    (s : A) (hs : s ∈ 𝒜 i) : Function.Surjective (Away.map f s) := by
  obtain ⟨D, hD⟩ := hf
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) y
  have hb' : b * f s ^ D ∈ ℬ ((n + D) • i) := by
    rw [add_smul]
    exact SetLike.mul_mem_graded hb (SetLike.pow_mem_graded D (map_mem f hs))
  obtain ⟨a, ha, hfa⟩ := hD ((n + D) • i)
    (by simpa using (Nat.le_add_left D n).trans (Nat.le_mul_of_pos_right (n + D) hi))
    (b * f s ^ D) hb'
  refine ⟨Away.mk 𝒜 hs (n + D) a ha, ?_⟩
  rw [Away.map_mk, ← awayMk_mul_pow (map_mem f hs) n D hb hb',
    HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk, hfa]

/-- **`Proj.map f` is a closed immersion**, provided every chart comparison is one. Being a closed
immersion is Zariski-local at the target, the standard affine charts `Spec (Away 𝒜 s)` cover
`Proj 𝒜`, and over each of them `Proj.map f` is the chart comparison
`Spec (Away ℬ (f s)) ⟶ Spec (Away 𝒜 s)` by
`AlgebraicGeometry.Proj.isPullback_awayι_map`. -/
theorem isClosedImmersion_map (hf : ℬ₊ ≤ 𝒜₊.map f)
    (H : ∀ {i : ℕ} (_hi : 0 < i) (s : A) (_hs : s ∈ 𝒜 i),
      IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s)))) :
    IsClosedImmersion (Proj.map f hf) := by
  refine IsZariskiLocalAtTarget.of_openCover (affineOpenCover 𝒜).openCover ?_
  rintro ⟨i, a⟩
  have hsq := (isPullback_awayι_map f hf i.2 (a : A) a.2).flip
  change IsClosedImmersion (pullback.snd (Proj.map f hf) (awayι 𝒜 (a : A) a.2 i.2))
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hsq.isoPullback.hom _).mp ?_
  have h := H i.2 (a : A) a.2
  rw [← hsq.isoPullback_hom_snd] at h
  exact h

/-- **Stacks tag 01N0, part (2).** If `𝒜 d ⟶ ℬ d` is surjective for all `d ≫ 0`, then
`Proj.map f : Proj ℬ ⟶ Proj 𝒜` is a closed immersion. -/
theorem isClosedImmersion_map_of_surjectiveInLargeDegrees (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hfd : SurjectiveInLargeDegrees f) : IsClosedImmersion (Proj.map f hf) :=
  isClosedImmersion_map hf fun hi s hs ↦
    IsClosedImmersion.spec_of_surjective _ (surjective_awayMap f hfd hi s hs)

/-- **`Proj` of a graded quotient is a closed subscheme of `Proj`.** For a surjective homomorphism
`f : 𝒜 →+*ᵍ ℬ` of graded rings — in particular for the quotient of a graded ring by a homogeneous
ideal — the induced morphism `Proj ℬ ⟶ Proj 𝒜` is everywhere defined and a closed immersion. -/
@[ega "II 2.9.2" "(i), special case", ega "II 3.6.2" "(i), special case"]
theorem isClosedImmersion_map_of_surjective (hf : ℬ₊ ≤ 𝒜₊.map f) (hfs : Function.Surjective f) :
    IsClosedImmersion (Proj.map f hf) :=
  isClosedImmersion_map_of_surjectiveInLargeDegrees hf (.of_surjective hfs)

end AlgebraicGeometry.Proj

end
