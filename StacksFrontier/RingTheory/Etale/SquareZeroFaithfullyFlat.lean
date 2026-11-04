module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Faithful flatness across a nilpotent thickening, and effective descent of elements

Two facts used by the first-order case of Stacks 05ZR, where an étale chart of a first-order
thickening is compared with the chart of its reduction.

## Main results

* `RingHom.FaithfullyFlat.of_surjective_of_isNilpotent_ker`: a flat ring map `A → B` whose
  reduction modulo a nil ideal of `A` factors as `A → A₀ → B₀` through a faithfully flat
  `A₀ → B₀` is faithfully flat, because the primes of `A` are those of `A₀`.
* `RingHom.mem_range_of_isPushout_of_faithfullyFlat`: for a faithfully flat `A₀ → B₀` and a
  pushout square presenting `B₀ ⊗_{A₀} B₀`, an element of `B₀` equalized by its two maps comes
  from `A₀` (faithfully flat descent of elements, `Algebra.IsEffective.of_faithfullyFlat`).

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory

universe u

/-- **Faithful flatness across a nilpotent kernel.** Let `ι : A → B` be flat and let
`ψ : A → A₀` be surjective with nil kernel. If `qB ∘ ι = φ ∘ ψ` for a faithfully flat
`φ : A₀ → B₀`, then `ι` is faithfully flat: every prime of `A` contains `ker ψ`, so it is the
inverse image of a prime of `A₀`, which lies under a prime of `B₀`, whose inverse image in `B`
lies over the given prime. -/
theorem RingHom.FaithfullyFlat.of_surjective_of_isNilpotent_ker {A A₀ B B₀ : Type*}
    [CommRing A] [CommRing A₀] [CommRing B] [CommRing B₀] (ι : A →+* B) (hι : ι.Flat)
    (ψ : A →+* A₀) (hψ : Function.Surjective ψ) (qB : B →+* B₀) (φ : A₀ →+* B₀)
    (hφψ : φ.comp ψ = qB.comp ι) (hφ : φ.FaithfullyFlat)
    (hnil : ∀ x ∈ RingHom.ker ψ, IsNilpotent x) : ι.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective] at hφ ⊢
  refine ⟨hι, fun p => ?_⟩
  obtain ⟨p₀, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [range_comap_of_surjective (R := A) (S := A₀) (f := ψ) (hf := hψ),
      PrimeSpectrum.mem_zeroLocus]
    intro x hx
    obtain ⟨n, hn⟩ := hnil x hx
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  obtain ⟨q₀, rfl⟩ := hφ.2 p₀
  refine ⟨PrimeSpectrum.comap qB q₀, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, ← hφψ, PrimeSpectrum.comap_comp_apply]

/-- **Faithfully flat descent of an element.** Let `φ : A₀ → B₀` be faithfully flat and let
`d₀', d₁' : B₀ → C₀` exhibit `C₀` as the pushout of `φ` along itself. An element `x` of `B₀` with
`d₀' x = d₁' x` is in the image of `φ`: the pushout is `B₀ ⊗_{A₀} B₀` with `d₀'` and `d₁'` the two
inclusions, so `x ⊗ 1 = 1 ⊗ x`, and the equalizer of the two inclusions is the image of `A₀`. -/
theorem RingHom.mem_range_of_isPushout_of_faithfullyFlat {A₀ B₀ C₀ : Type u} [CommRing A₀]
    [CommRing B₀] [CommRing C₀] (φ : A₀ →+* B₀) (hφ : φ.FaithfullyFlat) (d₀' d₁' : B₀ →+* C₀)
    (hC : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom φ) (CommRingCat.ofHom d₀')
      (CommRingCat.ofHom d₁'))
    {x : B₀} (hx : d₀' x = d₁' x) : x ∈ Set.range φ := by
  let : Algebra A₀ B₀ := φ.toAlgebra
  have : Module.FaithfullyFlat A₀ B₀ := hφ
  let e := (CommRingCat.isPushout_tensorProduct A₀ B₀ B₀).isoIsPushout _ _ hC
  have hl : e.hom (x ⊗ₜ[A₀] 1) = d₀' x := congrArg (fun g => g.hom x)
    (IsPushout.inl_isoIsPushout_hom (h := CommRingCat.isPushout_tensorProduct A₀ B₀ B₀) (h' := hC))
  have hr : e.hom (1 ⊗ₜ[A₀] x) = d₁' x := congrArg (fun g => g.hom x)
    (IsPushout.inr_isoIsPushout_hom (h := CommRingCat.isPushout_tensorProduct A₀ B₀ B₀) (h' := hC))
  have hxx : x ⊗ₜ[A₀] (1 : B₀) = 1 ⊗ₜ x :=
    (ConcreteCategory.bijective_of_isIso e.hom).1 (hl.trans (hx.trans hr.symm))
  have hmem : x ∈ (RingHom.eqLocus
      (Algebra.TensorProduct.includeLeftRingHom (R := A₀) (A := B₀) (B := B₀))
      (Algebra.TensorProduct.includeRight (R := A₀) (A := B₀) (B := B₀)).toRingHom : Set B₀) :=
    hxx
  rwa [(Algebra.IsEffective.of_faithfullyFlat (R := A₀) (S := B₀)).eqLocus_includeLeft_includeRight]
    at hmem
