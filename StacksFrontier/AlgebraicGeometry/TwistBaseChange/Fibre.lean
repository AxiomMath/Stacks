module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProjGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Pointwise base change for a graded localization away from a degree-zero element

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which exhibits `B` as a
localization of `A` away from an element `g` of degree `0`. This file proves the *pointwise*
consequences: the comparison of a single fibre of the twisting sheaves, and the lifting of a
single homogeneous fraction, together with the description of the induced morphism of `Proj` as
an open immersion onto `D₊(g)`.

## Main results

* `Stacks.AlgebraicGeometry.TwistBaseChange.bijective_fibreMap` and
  `bijective_twistFibreMap`: **the fibres agree.** The comparison map
  `Stacks.AlgebraicGeometry.ProjTwistCompare.fibreMap` on the fibres of the associated-module
  sheaves at a pair of homogeneous primes related by `ψ` is bijective — with no hypothesis on the
  primes at all.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isOpenImmersion_mapHom`: the induced morphism
  `U(ψ) ⟶ Proj 𝒜` is an open immersion.
* `Stacks.AlgebraicGeometry.TwistBaseChange.range_mapHom` and
  `Stacks.AlgebraicGeometry.TwistBaseChange.opensRange_mapHom`: **its image** is the standard
  open `D₊(g)`, equivalently the inverse image of `D(g) ⊆ Spec (𝒜 0)` under the structure
  morphism.
* `Stacks.AlgebraicGeometry.TwistBaseChange.exists_mem_twistGrading_mul_pow`: a homogeneous
  element for the `n`-th twist of `ℬ` becomes, after multiplication by a power of `ψ g`, the
  image of one for the `n`-th twist of `𝒜` *of the same twisted degree*.
* `Stacks.AlgebraicGeometry.TwistBaseChange.exists_fraction_lift`: **the fraction lifting.** A
  homogeneous fraction `b / s` of twisted degree `K` over `ℬ` is the `ψ`-image of a homogeneous
  fraction `β / c` of the same twisted degree `K` over `𝒜`, with `ψ c` a unit multiple of `s`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.notMem_of_isUnit_mul` and
  `notMem_base_of_notMem`: non-membership in an ideal is preserved by multiplying by a unit, and
  transfers from the image of a homogeneous element to the element itself.

## References

* [Stacks Project, Tag 01N3](https://stacks.math.columbia.edu/tag/01N3)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistChain Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.TwistBaseChange

attribute [local instance] ProjectiveSpectrum.isPrime

universe u w w'

section Pointwise

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The fibres -/

/-- **The fibres of the twisting sheaves agree.** If `ψ` exhibits `B` as a localization of `A`
away from `g`, then the comparison map on the fibres of the associated-module sheaves at a pair
of homogeneous primes related by `ψ` is bijective. -/
public theorem bijective_fibreMap (ψ : 𝒜 →+*ᵍ ℬ) (x : ProjectiveSpectrum 𝒜)
    (y : ProjectiveSpectrum ℬ) (h : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ψ)
    (g : A) [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom)
    [IsLocalization.Away g B] :
    Function.Bijective (fibreMap 𝒜 ℬ ψ x y h) := by
  have hIJ : x.asHomogeneousIdeal.toIdeal =
      (y.asHomogeneousIdeal.toIdeal).comap (algebraMap A B) := by
    rw [halg]
    exact congrArg HomogeneousIdeal.toIdeal h
  have hloc : IsLocalization.AtPrime (Localization.AtPrime y.asHomogeneousIdeal.toIdeal)
      ((y.asHomogeneousIdeal.toIdeal).comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers g) (Localization.AtPrime y.asHomogeneousIdeal.toIdeal)
      y.asHomogeneousIdeal.toIdeal
  have hpc : (x.asHomogeneousIdeal.toIdeal).primeCompl =
      (Ideal.comap (algebraMap A B) y.asHomogeneousIdeal.toIdeal).primeCompl :=
    Submonoid.ext fun a =>
      show a ∉ x.asHomogeneousIdeal.toIdeal ↔
        a ∉ Ideal.comap (algebraMap A B) y.asHomogeneousIdeal.toIdeal by rw [hIJ]
  have : IsLocalization (x.asHomogeneousIdeal.toIdeal).primeCompl
      (Localization.AtPrime y.asHomogeneousIdeal.toIdeal) := hpc ▸ hloc
  let e := IsLocalization.algEquiv (x.asHomogeneousIdeal.toIdeal).primeCompl
    (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)
    (Localization.AtPrime y.asHomogeneousIdeal.toIdeal)
  have he : Localization.localRingHom x.asHomogeneousIdeal.toIdeal
      y.asHomogeneousIdeal.toIdeal (ψ : A →+* B)
      (congrArg HomogeneousIdeal.toIdeal h) = e.toRingHom :=
    Localization.localRingHom_unique _ _ _ _ fun a => by
      refine (e.commutes a).trans ?_
      rw [IsScalarTower.algebraMap_apply A B
        (Localization.AtPrime y.asHomogeneousIdeal.toIdeal)]
      exact congrArg _ (congrArg (fun φ : A →+* B => φ a) halg)
  change Function.Bijective
    (Localization.localRingHom x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
      (ψ : A →+* B) (congrArg HomogeneousIdeal.toIdeal h))
  rw [he]
  exact e.bijective

/-- **The fibre comparison of the twisting sheaves is bijective at every point of `U(ψ)`.** -/
public theorem bijective_twistFibreMap (ψ : 𝒜 →+*ᵍ ℬ) (g : A) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B]
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    Function.Bijective (twistFibreMap 𝒜 ℬ ψ y) :=
  bijective_fibreMap 𝒜 ℬ ψ _ _ (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y) g halg

/-! ### Non-vanishing transfers -/

/-- If `v` does not lie in an ideal `J` and `u` is a unit, then `v * u` does not lie in `J`. -/
public theorem notMem_of_isUnit_mul {R : Type*} [CommRing R] {J : Ideal R} {u v : R}
    (hu : IsUnit u) (hv : v ∉ J) : v * u ∉ J :=
  (Ideal.mul_unit_mem_iff_mem J hu).not.mpr hv

/-- A homogeneous element of `𝒜` whose `ψ`-image is omitted by the prime at `y` is omitted by the
prime at the image point. -/
public theorem notMem_base_of_notMem (ψ : 𝒜 →+*ᵍ ℬ) {k : ℕ} {c : A} (hc : c ∈ 𝒜 k)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (h : ψ c ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal) :
    c ∉ (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal :=
  (notMem_mapHom_base_iff 𝒜 ℬ ψ y hc).mpr h

/-! ### Lifting a homogeneous fraction -/

/-- In a nonnegative twisted degree, a twisted homogeneous piece is a homogeneous piece of the
ring. -/
private theorem mem_twistGrading_iff_of_nonneg (ℛ : ℕ → σ) {n i : ℤ} (hi : 0 ≤ i + n) (x : A) :
    x ∈ twistGrading (S := A) ℛ n i ↔ x ∈ ℛ (i + n).toNat := by
  simp [integerGrading, hi]

/-- In a negative twisted degree, the twisted homogeneous piece is zero. -/
private theorem eq_zero_of_mem_twistGrading_of_neg (ℛ : ℕ → σ) {n i : ℤ} (hi : ¬ 0 ≤ i + n)
    {x : A} (hx : x ∈ twistGrading (S := A) ℛ n i) : x = 0 := by
  simpa [integerGrading, hi] using hx

/-- **Lifting a homogeneous element for a twist.** An element of `B` lying in the degree-`i` piece
of the `n`-th twist becomes, after multiplication by a power of `ψ g`, the `ψ`-image of an element
of `A` lying in the degree-`i` piece of the `n`-th twist — the *same* `i`. -/
public theorem exists_mem_twistGrading_mul_pow (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0)
    [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B]
    (n i : ℤ) {b : B} (hb : b ∈ twistGrading (S := B) ℬ n i) :
    ∃ (β : A) (k : ℕ), β ∈ twistGrading (S := A) 𝒜 n i ∧ ψ β = b * ψ g ^ k := by
  by_cases hi : 0 ≤ i + n
  · obtain ⟨a, k, ha, hak⟩ := exists_mem_graded_mul_pow 𝒜 ℬ ψ hg halg
      ((mem_twistGrading_iff_of_nonneg ℬ hi b).1 hb)
    exact ⟨a, k, (mem_twistGrading_iff_of_nonneg 𝒜 hi a).2 ha, hak⟩
  · have hb0 := eq_zero_of_mem_twistGrading_of_neg ℬ hi hb
    exact ⟨0, 0, zero_mem _, by rw [map_zero, hb0, zero_mul]⟩

omit [GradedRing ℬ] in
/-- Multiplying by a degree-zero element does not move the degree in a twisted grading. -/
public theorem mul_mem_twistGrading {n i : ℤ} {a x : A} (ha : a ∈ 𝒜 0)
    (hx : x ∈ twistGrading (S := A) 𝒜 n i) : a * x ∈ twistGrading (S := A) 𝒜 n i := by
  by_cases hi : 0 ≤ i + n
  · rw [mem_twistGrading_iff_of_nonneg 𝒜 hi] at hx ⊢
    simpa using SetLike.mul_mem_graded ha hx
  · rw [eq_zero_of_mem_twistGrading_of_neg 𝒜 hi hx, mul_zero]
    exact zero_mem _

/-- **The fraction lifting.** A homogeneous fraction `b / s` with numerator in the degree-`K`
piece of the `n`-th twist of `ℬ` and denominator in `ℬ K` is the `ψ`-image of a homogeneous
fraction `β / c` with numerator in the degree-`K` piece of the `n`-th twist of `𝒜` and
denominator in `𝒜 K`, the two being related by `s * ψ β = ψ c * b`; and `ψ c` is `s` times a
power of `ψ g`, hence a unit multiple of `s`. -/
public theorem exists_fraction_lift (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B]
    (n : ℤ) (K : ℕ) {b s : B} (hb : b ∈ twistGrading (S := B) ℬ n (K : ℤ)) (hs : s ∈ ℬ K) :
    ∃ (β c : A) (m : ℕ), β ∈ twistGrading (S := A) 𝒜 n (K : ℤ) ∧ c ∈ 𝒜 K ∧
      ψ c = s * ψ g ^ m ∧ s * ψ β = ψ c * b := by
  obtain ⟨β₀, j, hβ₀, hβ₀e⟩ := exists_mem_twistGrading_mul_pow 𝒜 ℬ ψ hg halg n (K : ℤ) hb
  obtain ⟨c₀, k, hc₀, hc₀e⟩ := exists_mem_graded_mul_pow 𝒜 ℬ ψ hg halg hs
  have hgk : g ^ k ∈ 𝒜 0 := by simpa using SetLike.pow_mem_graded k hg
  have hgj : g ^ j ∈ 𝒜 0 := by simpa using SetLike.pow_mem_graded j hg
  refine ⟨g ^ k * β₀, g ^ j * c₀, j + k, mul_mem_twistGrading 𝒜 hgk hβ₀, ?_, ?_, ?_⟩
  · simpa using SetLike.mul_mem_graded hgj hc₀
  · rw [map_mul, map_pow, hc₀e, pow_add]
    ring
  · rw [map_mul, map_mul, map_pow, map_pow, hβ₀e, hc₀e]
    ring

end Pointwise

/-! ### The induced morphism is an open immersion onto the locus where `g` is invertible -/

section OpenImmersion

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The induced morphism of a graded localization away from a degree-zero element is an open
immersion.** -/
@[stacks 01N3 "the open immersion"]
public theorem isOpenImmersion_mapHom (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    IsOpenImmersion (mapHom 𝒜 ℬ ψ) := by
  have hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ :=
    irrelevant_le_map_of_isLocalizationAway 𝒜 ℬ ψ hg halg
  have hdom : mapDomain 𝒜 ℬ ψ = ⊤ :=
    mapDomain_eq_top_of_isLocalizationAway 𝒜 ℬ ψ hg halg
  have htop : IsOpenImmersion (mapHomOfTop 𝒜 ℬ ψ hdom) := by
    rw [mapHomOfTop_eq_map 𝒜 ℬ ψ hψ hdom]
    exact RelativeProjGlue.isOpenImmersion_projMap 𝒜 ℬ ψ hg halg hψ
  rw [mapHomOfTop] at htop
  have h1 : IsOpenImmersion
      (((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom ≫ mapHom 𝒜 ℬ ψ) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
      (Scheme.topIso (AlgebraicGeometry.Proj ℬ)).inv _).mp htop
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
    ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom _).mp h1

/-- **The image of the induced morphism of a graded localization away from a degree-zero
element** is the standard open `D₊(g)` of `Proj 𝒜`. -/
public theorem range_mapHom (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    Set.range (mapHom 𝒜 ℬ ψ).base = (Proj.basicOpen 𝒜 g : Set (AlgebraicGeometry.Proj 𝒜)) := by
  have hdom : mapDomain 𝒜 ℬ ψ = ⊤ := mapDomain_eq_top_of_isLocalizationAway 𝒜 ℬ ψ hg halg
  have hu : IsUnit (ψ g) := isUnit_of_isLocalizationAway 𝒜 ℬ ψ g halg
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    change g ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal
    rw [notMem_mapHom_base_iff 𝒜 ℬ ψ y hg]
    intro hmem
    change ψ g ∈ (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.toIdeal at hmem
    exact (y.1 : ProjectiveSpectrum ℬ).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · intro hp
    change g ∉ p.asHomogeneousIdeal.toIdeal at hp
    have hdisj : Disjoint (Submonoid.powers g : Set A)
        (p.asHomogeneousIdeal.toIdeal : Set A) := by
      rw [Set.disjoint_left]
      rintro z ⟨k, rfl⟩ hz
      exact hp (p.isPrime.mem_of_pow_mem _ hz)
    have hcomap : (p.asHomogeneousIdeal.map ψ).comap ψ = p.asHomogeneousIdeal := by
      refine HomogeneousIdeal.toIdeal_injective ?_
      have h := IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers g) B p.isPrime hdisj
      rwa [Ideal.under_def, halg] at h
    have hprime : (p.asHomogeneousIdeal.map ψ).toIdeal.IsPrime := by
      have h := IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers g) B p.asHomogeneousIdeal.toIdeal p.isPrime hdisj
      rwa [halg] at h
    have hirr : ¬ HomogeneousIdeal.irrelevant ℬ ≤ p.asHomogeneousIdeal.map ψ := by
      obtain ⟨d, f, hd, hf, hfp⟩ := exists_homogeneous_pos_notMem 𝒜 p
      intro hle
      refine hfp ?_
      have hmem : f ∈ (p.asHomogeneousIdeal.map ψ).comap ψ :=
        hle (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hd (ψ.map_mem hf))
      rwa [hcomap] at hmem
    refine ⟨⟨⟨p.asHomogeneousIdeal.map ψ, hprime, hirr⟩, by rw [hdom]; trivial⟩, ?_⟩
    exact ProjectiveSpectrum.ext ((mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ _).trans hcomap)

/-- For a graded ring homomorphism exhibiting `B` as a localization of `A` away from an element
`g` of degree `0`, the open immersion `Proj ℬ ⟶ Proj 𝒜` identifies `Proj ℬ` with the inverse
image of the standard open `D(g) ⊆ Spec (𝒜 0)` under the structure morphism
`AlgebraicGeometry.Proj.toSpecZero`. -/
@[stacks 01N3 "the inverse image of D(g)"]
public theorem opensRange_mapHom (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B]
    [IsOpenImmersion (mapHom 𝒜 ℬ ψ)] :
    (mapHom 𝒜 ℬ ψ).opensRange =
      Proj.toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen (⟨g, hg⟩ : 𝒜 0) :=
  TopologicalSpace.Opens.ext <| by
    rw [Proj.toSpecZero_preimage_basicOpen 𝒜 (⟨g, hg⟩ : 𝒜 0)]
    exact range_mapHom 𝒜 ℬ ψ hg halg

end OpenImmersion

end Stacks.AlgebraicGeometry.TwistBaseChange

end
