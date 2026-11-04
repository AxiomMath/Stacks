module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.RingTheory.Support
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension

/-!
# Local dimension across a map with a singleton fibre

An étale morphism preserves the local Krull dimension because it is open; a *finite* morphism
preserves it at a point whose fibre is that single point, because it is closed. This file proves
both the topological statement and its ring-theoretic consequence for the support of a module
along an integral extension.

The topological input is the same for both: a continuous closed surjection `f : X → Y` which is
injective on specialisations, at a point `x` with `f ⁻¹' {f x} = {x}`. Closedness replaces
openness in the role it plays for an étale morphism: for `≤` the neighbourhood of `f x` is pulled
back, exactly as in the open case, and for `≥` the neighbourhood `Y \ f(X \ A)` of `f x` — open
because `f` is closed, and containing `f x` because the fibre is the singleton `{x} ⊆ A` — has
its inverse image inside the prescribed neighbourhood `A` of `x`.

The ring-theoretic case is a module `M` finite over both rings of an integral extension `R → S`,
at a prime `p` of `S` which is the *only* prime contracting to `q = p ∩ R`. Contraction along an
integral map is closed and strictly monotone on primes, which is what supplies the two
hypotheses of the topological statement, and going up supplies the surjectivity.

## Main results

* `Topology.topologicalKrullDimAt_eq_of_isClosedMap_of_specializes_injective`: the local Krull
  dimension at a point with a singleton fibre is preserved by a continuous closed surjection
  injective on specialisations.
* `Module.topologicalKrullDimAt_support_eq_of_isIntegral`: the local dimension of the support of
  a module along an integral extension is unchanged at a prime over which there is exactly one
  prime upstairs.

## Implementation notes

`IsClosedMap.restrictOfIsClosed` is the bookkeeping that turns a closed map of ambient spaces
into a closed map of a closed subspace into a subspace containing its image; it is what lets the
topological statement be applied to the supports, which are closed subspaces of the prime
spectra rather than whole spaces.

Primes of `S` are compared through `PrimeSpectrum.le_iff_specializes`, so that specialisation in
the subspace topology on the support is read off from inclusion of ideals;
`Ideal.IsIntegral.comap_lt_comap` is then exactly injectivity on specialisations. Surjectivity
onto the support downstairs is `Ideal.exists_ideal_over_prime_of_isIntegral` applied to the
annihilator of `M`, whose contraction is the annihilator downstairs.

## References

* [Stacks Project, Tag 00OK](https://stacks.math.columbia.edu/tag/00OK)
* [Stacks Project, Tag 02JF](https://stacks.math.columbia.edu/tag/02JF)
-/

@[expose] public section

open TopologicalSpace

/-- A closed map restricts to a closed map from a closed subset of its source to any subset of
its target that contains the image of that closed subset. -/
theorem IsClosedMap.restrictOfIsClosed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsClosedMap f) {T : Set X} (hT : IsClosed T) {T' : Set Y}
    (hmaps : ∀ x ∈ T, f x ∈ T') :
    IsClosedMap (fun z : T ↦ (⟨f z.1, hmaps z.1 z.2⟩ : T')) := by
  intro C hC
  obtain ⟨C₀, hC₀, hCeq⟩ := isClosed_induced_iff.mp hC
  rw [isClosed_induced_iff]
  refine ⟨f '' (C₀ ∩ T), hf _ (hC₀.inter hT), ?_⟩
  ext w
  simp only [Set.mem_preimage, Set.mem_image]
  exact ⟨fun ⟨x, ⟨hxC₀, hxT⟩, hxw⟩ ↦ ⟨⟨x, hxT⟩, by rw [← hCeq]; exact hxC₀, Subtype.ext hxw⟩,
    fun ⟨z, hzC, hzw⟩ ↦ ⟨z.1, ⟨by rwa [← hCeq] at hzC, z.2⟩, congrArg Subtype.val hzw⟩⟩

namespace Topology

/-- A continuous closed surjection between sober Kolmogorov spaces which is injective on
specialisations preserves the local Krull dimension at any point whose fibre is that single
point. This is the closed-map counterpart of
`Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective`. -/
theorem topologicalKrullDimAt_eq_of_isClosedMap_of_specializes_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] [T0Space X] [T0Space Y]
    (f : X → Y) (hcont : Continuous f) (hclosed : IsClosedMap f)
    (hsurj : Function.Surjective f)
    (hinj : ∀ ⦃x y : X⦄, x ⤳ y → f x = f y → x = y)
    (x : X) (hfib : f ⁻¹' {f x} = {x}) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) := by
  show (⨅ A : {A : Set X // x ∈ A ∧ IsOpen A}, topologicalKrullDim (↥A.1)) =
    ⨅ B : {B : Set Y // f x ∈ B ∧ IsOpen B}, topologicalKrullDim (↥B.1)
  refine le_antisymm (le_iInf fun B ↦ ?_) (le_iInf fun A ↦ ?_)
  · -- Pull the neighbourhood of `f x` back; the comparison is injectivity on specialisations.
    let A : {A : Set X // x ∈ A ∧ IsOpen A} :=
      ⟨f ⁻¹' B.1, by simpa using B.2.1, B.2.2.preimage hcont⟩
    have : QuasiSober ↥A.1 := A.2.2.isOpenEmbedding_subtypeVal.quasiSober
    refine (iInf_le _ A).trans
      (topologicalKrullDim_le_of_continuous_of_specializes_injective
        (Subtype.map f fun _ hz ↦ hz) (hcont.subtype_map _)
        fun z w hzw hEq ↦ Subtype.ext
          (hinj ((subtype_specializes_iff z w).mp hzw) (congrArg Subtype.val hEq)))
  · -- The complement of the image of the complement is a neighbourhood of `f x` whose inverse
    -- image sits inside `A`; the comparison is the lifting of specialisations.
    have hVopen : IsOpen ((f '' A.1ᶜ)ᶜ) :=
      (hclosed _ (isClosed_compl_iff.mpr A.2.2)).isOpen_compl
    have hxV : f x ∈ (f '' A.1ᶜ)ᶜ := by
      rintro ⟨w, hw, hfw⟩
      have hwx : w ∈ ({x} : Set X) := by rw [← hfib]; exact hfw
      exact hw (hwx ▸ A.2.1)
    have hpre : f ⁻¹' (f '' A.1ᶜ)ᶜ ⊆ A.1 := fun z hz ↦ by
      by_contra hzA
      exact hz ⟨z, hzA, rfl⟩
    have : QuasiSober ↥((f '' A.1ᶜ)ᶜ) := hVopen.isOpenEmbedding_subtypeVal.quasiSober
    have : QuasiSober ↥(f ⁻¹' (f '' A.1ᶜ)ᶜ) :=
      (hVopen.preimage hcont).isOpenEmbedding_subtypeVal.quasiSober
    refine (iInf_le _ (⟨(f '' A.1ᶜ)ᶜ, hxV, hVopen⟩ :
      {B : Set Y // f x ∈ B ∧ IsOpen B})).trans ?_
    refine le_trans (topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
      (Subtype.map f fun _ hz ↦ hz) (hcont.subtype_map _) (fun b ↦ ?_)
      (Or.inl fun z b hzb ↦ ?_)) ?_
    · obtain ⟨z, hz⟩ := hsurj b.1
      exact ⟨⟨z, hz ▸ b.2⟩, Subtype.ext hz⟩
    · have hzb' : (⟨f z.1, z.2⟩ : ↥((f '' A.1ᶜ)ᶜ)) ⤳ b := hzb
      obtain ⟨w, hzw, hfw⟩ :=
        hclosed.specializingMap ((subtype_specializes_iff _ _).mp hzb')
      exact ⟨⟨w, hfw ▸ b.2⟩,
        (subtype_specializes_iff _ _).2 hzw, Subtype.ext hfw⟩
    · exact Topology.IsInducing.topologicalKrullDim_le
        (Topology.IsEmbedding.inclusion hpre).isInducing

end Topology

namespace Module

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- The annihilator of a module over the base of a scalar tower is the contraction of its
annihilator over the top: a scalar from the base acts through its image. -/
theorem annihilator_eq_comap_annihilator :
    Module.annihilator R M = (Module.annihilator S M).comap (algebraMap R S) := by
  ext a
  simp [Module.mem_annihilator]

/-- A prime in the support of a module over the top of a scalar tower contracts into the
support of the same module over the base. -/
theorem comap_mem_support [Module.Finite R M] [Module.Finite S M] {p : PrimeSpectrum S}
    (hp : p ∈ Module.support S M) :
    PrimeSpectrum.comap (algebraMap R S) p ∈ Module.support R M := by
  rw [Module.mem_support_iff_of_finite] at hp ⊢
  rw [PrimeSpectrum.comap_asIdeal, annihilator_eq_comap_annihilator (S := S) (M := M)]
  exact Ideal.comap_mono hp

/-- **The local dimension of the support is unchanged by an integral extension at a prime with
a unique prime above it.** Let `R → S` be integral, let `M` be a module finite over both, let
`p` be a prime of `S` and `q` its contraction to `R`, and assume `p` is the only prime of `S`
contracting to `q`. Then the support of `M` over `S` has, at `p`, the local Krull dimension that
the support of `M` over `R` has at `q`.

This is the ring-theoretic form of the statement that a finite morphism whose fibre over a point
is a single point does not change the local dimension of the support of a finite module there. -/
theorem topologicalKrullDimAt_support_eq_of_isIntegral [Module.Finite R M] [Module.Finite S M]
    [Algebra.IsIntegral R S] (p : PrimeSpectrum S) (q : PrimeSpectrum R)
    (hpq : PrimeSpectrum.comap (algebraMap R S) p = q)
    (huniq : ∀ p' : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) p' = q → p' = p)
    (hp : p ∈ Module.support S M) (hq : q ∈ Module.support R M) :
    topologicalKrullDimAt (Module.support S M) ⟨p, hp⟩ =
      topologicalKrullDimAt (Module.support R M) ⟨q, hq⟩ := by
  subst hpq
  have hmaps : ∀ p' ∈ Module.support S M,
      PrimeSpectrum.comap (algebraMap R S) p' ∈ Module.support R M :=
    fun _ h ↦ comap_mem_support h
  have hintegral : (algebraMap R S).IsIntegral := fun s ↦ Algebra.IsIntegral.isIntegral s
  have hTclosed : IsClosed (Module.support S M) := Module.isClosed_support
  have : QuasiSober (Module.support S M) := hTclosed.isClosedEmbedding_subtypeVal.quasiSober
  have : QuasiSober (Module.support R M) :=
    Module.isClosed_support.isClosedEmbedding_subtypeVal.quasiSober
  refine Topology.topologicalKrullDimAt_eq_of_isClosedMap_of_specializes_injective
    (Subtype.map (PrimeSpectrum.comap (algebraMap R S)) hmaps)
    ((PrimeSpectrum.continuous_comap (algebraMap R S)).subtype_map _)
    (IsClosedMap.restrictOfIsClosed
      (PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S) hintegral)
      hTclosed hmaps)
    (fun w ↦ ?_) (fun z w hzw hEq ↦ ?_) ⟨p, hp⟩ ?_
  · -- Going up: every prime in the support downstairs is the contraction of one upstairs.
    have hann : (Module.annihilator S M).comap (algebraMap R S) ≤ w.1.asIdeal := by
      rw [← annihilator_eq_comap_annihilator (S := S) (M := M)]
      exact Module.mem_support_iff_of_finite.mp w.2
    have : w.1.asIdeal.IsPrime := w.1.isPrime
    obtain ⟨P, hPge, hPprime, hPcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral w.1.asIdeal (Module.annihilator S M) hann
    exact ⟨⟨⟨P, hPprime⟩, Module.mem_support_iff_of_finite.mpr hPge⟩,
      Subtype.ext (PrimeSpectrum.ext hPcomap)⟩
  · -- Contraction along an integral map is strictly monotone, hence injective on
    -- specialisations.
    have hle : z.1 ≤ w.1 := (PrimeSpectrum.le_iff_specializes z.1 w.1).mpr
      ((subtype_specializes_iff z w).mp hzw)
    rcases eq_or_lt_of_le hle with h | hlt
    · exact Subtype.ext h
    · have : z.1.asIdeal.IsPrime := z.1.isPrime
      exact absurd (congrArg (fun v : Module.support R M ↦ v.1.asIdeal) hEq)
        (Ideal.IsIntegral.comap_lt_comap (R := R)
          ((PrimeSpectrum.asIdeal_lt_asIdeal z.1 w.1).mpr hlt)).ne
  · -- The fibre of the contraction over `q` is the single prime `p`.
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext (huniq z.1 (congrArg (fun v : Module.support R M ↦ v.1) h)),
      fun h ↦ by rw [h]⟩

end Module

end
