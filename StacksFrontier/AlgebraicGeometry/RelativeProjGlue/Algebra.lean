module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison

/-!
# Degree-zero localizations of a graded localization

Tag 01NO asks for the square of projective spectra attached to a nested pair of affine opens of
the base to be cartesian. Read on the standard affine cover of `Proj`, that question becomes a
single statement of commutative algebra, and this file proves it: if `ψ : 𝒜 →+*ᵍ ℬ` exhibits `B`
as a localization of `A` away from an element `s` of degree `0`, then for every homogeneous
`f : A` the induced map of degree-zero localizations
`AlgebraicGeometry.HomogeneousLocalization.Away.map ψ f : A⁰_f → B⁰_{ψ f}` exhibits `B⁰_{ψ f}` as
the localization of `A⁰_f` away from the single degree-zero element `s / 1`.

Geometrically: the standard chart `Spec B⁰_{ψ f}` of `Proj ℬ` is the locus inside the standard
chart `Spec A⁰_f` of `Proj 𝒜` where `s` is invertible. That is the whole content of the cartesian
square, and the geometry built from it is in
`StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Basic`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGlue.isUnit_of_isUnit_coe`: a degree-zero element of a
  graded ring which is a unit of the whole ring is a unit of the degree-zero subring — i.e. its
  inverse again has degree zero.
* `Stacks.AlgebraicGeometry.RelativeProjGlue.isLocalization_away_map`: the statement above,
  `B⁰_{ψ f} = (A⁰_f)[1/(s/1)]`.

## Implementation notes

The three halves of `IsLocalization` are discharged in the order they are stored in
`Submonoid.IsLocalizationMap`, following the shape of Mathlib's
`AlgebraicGeometry.HomogeneousLocalization.Away.isLocalization_mul`, which is the analogous
statement for a localization taking place *inside* one graded ring.

* That `s / 1` becomes a unit is where the degree-zero unit lemma is used. The element `ψ s` is a
  unit of `B` because `B` is a localization of `A` away from `s`, but to invert `s / 1` inside
  the degree-zero localization one needs the inverse of `ψ s` to lie in degree zero as well. The
  lemma is a one-liner once one notices that `GradedRing.projZeroRingHom'` is a *ring*
  homomorphism `B →+* ℬ 0` which fixes degree-zero elements, so `IsUnit.map` applies; it is
  absent from Mathlib, whose `Mathlib/RingTheory/GradedAlgebra/` directory contains no statement
  about units at all.
* Surjectivity is `Stacks.AlgebraicGeometry.RelativeProj.exists_mem_graded_mul_pow`: an element
  of `B⁰_{ψ f}` is `b / (ψ f) ^ n` with `b` homogeneous of degree `n • d`, and that lemma
  produces a numerator in `A` of the *same* degree after multiplying by a power of `ψ s`.
* Injectivity transports a relation `(ψ f) ^ j * (…) = 0` from `B` back to `A` through
  `IsLocalization.exists_of_eq` for the submonoid of powers of `s`, and then clears the powers of
  `f`, which are invertible in `A⁰_f`.

The denominator of `AlgebraicGeometry.HomogeneousLocalization.fromZeroRingHom` is the unit of the
submonoid rather than the element `1 : A`, so `val_fromZeroRingHom` is stated and used instead of
unfolding the definition by `simp`: unfolding leaves the anonymous constructor in place and the
subsequent `Localization.mk` rewrites then fail to match it.

The degree of `f` is *not* assumed positive. Positivity is what makes the chart `Spec A⁰_f` an
open of `Proj 𝒜`, which is a geometric question; the ring-theoretic statement needs none of it.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)

## Not done here

Nothing geometric: no morphism of schemes occurs in this file. The general base-change statement
of Tag 01N2, for an arbitrary ring map rather than a localization at a degree-zero element, is
not proved and is not needed: the morphisms of
`AlgebraicGeometry.Scheme.AffineZariskiSite` are basic-open inclusions, so only this case arises.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjGlue

universe u w w'

section GradeZero

variable {B : Type u} {τ : Type w'} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

/-- **A degree-zero unit of a graded ring has a degree-zero inverse.** An element of `ℬ 0` whose
image in `B` is a unit is already a unit of the degree-zero subring `ℬ 0`.

The inverse is produced by the degree-zero projection, which is a ring homomorphism `B →+* ℬ 0`
and is the identity on elements that already have degree zero. -/
public theorem isUnit_of_isUnit_coe {b : ℬ 0} (hb : IsUnit (b : B)) : IsUnit b := by
  have h := hb.map (GradedRing.projZeroRingHom' ℬ)
  rwa [GradedRing.projZeroRingHom'_apply_coe] at h

end GradeZero

section Val

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The fraction underlying the image of a degree-zero element in a homogeneous localization:
`a / 1`, with denominator the unit of the submonoid. -/
public theorem val_fromZeroRingHom (x : Submonoid A) (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 x a).val = Localization.mk (a : A) 1 := rfl

end Val

section Brick

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The commutative-algebra content of Tag 01NO.** Let `ψ : 𝒜 →+*ᵍ ℬ` exhibit `B` as a
localization of `A` away from an element `s` of degree `0`, and let `f : A` be homogeneous. Then
the induced map of degree-zero localizations
`AlgebraicGeometry.HomogeneousLocalization.Away.map ψ f` exhibits `B⁰_{ψ f}` as the localization
of `A⁰_f` away from the degree-zero element `s / 1`.

Geometrically: the standard chart `Spec B⁰_{ψ f}` of `Proj ℬ` is the open subscheme of the
standard chart `Spec A⁰_f` of `Proj 𝒜` on which `s` is invertible. This is what makes the square
of Tag 01NO cartesian. -/
public theorem isLocalization_away_map (ψ : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 0)
    [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away s B]
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) :
    letI := (Away.map ψ f).toAlgebra
    IsLocalization.Away
      (fromZeroRingHom 𝒜 (Submonoid.powers f) ⟨s, hs⟩) (Away ℬ (ψ f)) := by
  let := (Away.map ψ f).toAlgebra
  have hap : ∀ x : Away 𝒜 f, algebraMap (Away 𝒜 f) (Away ℬ (ψ f)) x = Away.map ψ f x :=
    fun x => rfl
  set g : Away 𝒜 f := fromZeroRingHom 𝒜 (Submonoid.powers f) ⟨s, hs⟩ with hgdef
  have hmapg : Away.map ψ f g = fromZeroRingHom ℬ (Submonoid.powers (ψ f))
      (zeroHom 𝒜 ℬ ψ ⟨s, hs⟩) := by
    have := congr($(awayMap_comp_fromZeroRingHom 𝒜 ℬ ψ f) (⟨s, hs⟩ : 𝒜 0))
    simpa [hgdef] using this
  have hunit : IsUnit (zeroHom 𝒜 ℬ ψ (⟨s, hs⟩ : 𝒜 0)) := by
    refine isUnit_of_isUnit_coe ℬ ?_
    rw [coe_zeroHom_apply]
    exact isUnit_of_isLocalizationAway 𝒜 ℬ ψ s halg
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, k, rfl⟩
    change IsUnit (algebraMap (Away 𝒜 f) (Away ℬ (ψ f)) (g ^ k))
    rw [hap, map_pow, hmapg]
    exact (hunit.map (fromZeroRingHom ℬ (Submonoid.powers (ψ f)))).pow k
  · intro z
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (ψ.map_mem hf) z
    obtain ⟨a, k, ha, hak⟩ := exists_mem_graded_mul_pow 𝒜 ℬ ψ hs halg hb
    refine ⟨⟨Away.mk 𝒜 hf n a ha, ⟨g ^ k, k, rfl⟩⟩, ?_⟩
    simp only [hap, map_pow, hmapg, Away.map_mk]
    ext
    simp only [val_mul, val_pow, Away.val_mk, val_fromZeroRingHom, coe_zeroHom_apply,
      Localization.mk_pow, one_pow, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, mul_one, GradedRingHom.coe_toRingHom, hak]
  · intro x y hxy
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
    obtain ⟨m, a', ha', rfl⟩ := Away.mk_surjective 𝒜 hf y
    simp only [hap, Away.map_mk] at hxy
    replace hxy := congrArg HomogeneousLocalization.val hxy
    simp only [Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hxy
    obtain ⟨⟨c, j, rfl⟩, hc⟩ := hxy
    have hmapA : ∀ x : A, algebraMap A B x = ψ x := fun x =>
      congrArg (fun φ : A →+* B => φ x) halg
    have heq : algebraMap A B (f ^ j * (f ^ m * a)) = algebraMap A B (f ^ j * (f ^ n * a')) := by
      simp only [hmapA, map_mul, map_pow]
      simpa using hc
    obtain ⟨⟨c, i, rfl⟩, hi⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers s) heq
    refine ⟨⟨g ^ i, i, rfl⟩, ?_⟩
    ext
    simp only [val_mul, val_pow, Away.val_mk, hgdef, val_fromZeroRingHom,
      Localization.mk_pow, one_pow, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨⟨f ^ j, j, rfl⟩, ?_⟩
    simp only [one_mul]
    linear_combination hi

end Brick

end Stacks.AlgebraicGeometry.RelativeProjGlue

end
