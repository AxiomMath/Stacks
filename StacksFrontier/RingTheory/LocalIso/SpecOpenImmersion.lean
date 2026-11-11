module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.LocalIso

import StacksCore.Tactic.StacksAttribute

/-!
# Local isomorphisms of rings, as open immersions of spectra

A ring map `A → B` is a *local isomorphism* in the sense of Stacks if for every prime `𝔮` of `B`
there is `g ∈ B`, `g ∉ 𝔮`, such that `Spec(B_g) → Spec(A)` is an open immersion. This file
states that definition and identifies it with Mathlib's `Algebra.IsLocalIso`, which asks instead
that each such `B_g` be a *standard* open immersion over `A`, i.e. a localization `A_f`.

## Main definitions

* `Algebra.IsLocalIsomorphism`: part (1) of Stacks 096E, as stated in the source.

## Main results

* `Algebra.isStandardOpenImmersion_of_isOpenImmersion`: if `Spec(C) → Spec(A)` is an open
  immersion whose image contains the basic open `D(a)`, then `C_a` is a standard open immersion
  over `A`; it is isomorphic to `A_a`.
* `Algebra.isLocalIsomorphism_iff_isLocalIso`: the Stacks definition agrees with
  `Algebra.IsLocalIso`.

## Implementation notes

The bridge shrinks along basic opens: given `g ∉ 𝔮` with `Spec(B_g) → Spec(A)` an open immersion,
the image of `𝔮` lies in a basic open `D(a)` inside the image, and the element `g · a` of `B` is
again outside `𝔮`, with `B_{g a} ≅ A_a` over `A`.

Part (2) of Stacks 096E, *identifies local rings*, is `Algebra.IdentifiesLocalRings` in
`StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings`.

## References

* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Algebra

/-- A ring map `A → B` is a *local isomorphism* if for every prime `q` of `B` there is `g ∉ q`
such that `Spec(B_g) → Spec(A)` is an open immersion. This is the definition as stated in the
source; `Algebra.isLocalIsomorphism_iff_isLocalIso` identifies it with `Algebra.IsLocalIso`. -/
@[stacks 096E "part (1): local isomorphism, as stated in the source; equivalent to
`Algebra.IsLocalIso` by `Algebra.isLocalIsomorphism_iff_isLocalIso`"]
def IsLocalIsomorphism (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (q : Ideal B) [q.IsPrime], ∃ g ∉ q,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))))

/-- If `Spec(C) → Spec(A)` is an open immersion whose image contains the basic open `D(a)`,
then the localization of `C` at the image of `a` is a standard open immersion over `A`. -/
theorem isStandardOpenImmersion_of_isOpenImmersion {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] [Algebra C D] [Algebra A D] [IsScalarTower A C D]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A C)))] (a : A)
    [IsLocalization.Away (algebraMap A C a) D]
    (ha : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap A C))) :
    IsStandardOpenImmersion A D := by
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap A D)) = PrimeSpectrum.basicOpen a := by
    rw [IsScalarTower.algebraMap_eq A C D, PrimeSpectrum.comap_comp, Set.range_comp,
      PrimeSpectrum.localization_away_comap_range D (algebraMap A C a)]
    exact Set.image_preimage_eq_of_subset ha
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A D))) := by
    rw [IsScalarTower.algebraMap_eq A C D, CommRingCat.ofHom_comp, Spec.map_comp]
    have := IsOpenImmersion.of_isLocalization (algebraMap A C a) (S := D)
    infer_instance
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A D))) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).trans hrange.symm
  let e := IsOpenImmersion.isoOfRangeEq _ _ hr
  let φ : CommRingCat.of (Localization.Away a) ⟶ CommRingCat.of D := Spec.preimage e.inv
  let ψ : CommRingCat.of D ⟶ CommRingCat.of (Localization.Away a) := Spec.preimage e.hom
  have h₁ : φ ≫ ψ = 𝟙 _ := Spec.map_injective (by simp [φ, ψ])
  have h₂ : ψ ≫ φ = 𝟙 _ := Spec.map_injective (by simp [φ, ψ])
  have hc : CommRingCat.ofHom (algebraMap A (Localization.Away a)) ≫ φ =
      CommRingCat.ofHom (algebraMap A D) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hr
  let i : CommRingCat.of (Localization.Away a) ≅ CommRingCat.of D := ⟨φ, ψ, h₁, h₂⟩
  refine .of_algEquiv (AlgEquiv.ofRingEquiv (f := i.commRingCatIsoToRingEquiv) fun x ↦ ?_)
  change φ.hom (algebraMap A (Localization.Away a) x) = algebraMap A D x
  exact congrArg (fun h ↦ h.hom x) hc

/-- **Stacks 096E, part (1).** The source's definition of a local isomorphism, asking that each
`Spec(B_g) → Spec(A)` be an open immersion, agrees with Mathlib's `Algebra.IsLocalIso`, asking
that each `B_g` be a standard open immersion over `A`. -/
@[stacks 096E "part (1): the source's local isomorphism is `Algebra.IsLocalIso`"]
theorem isLocalIsomorphism_iff_isLocalIso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] : IsLocalIsomorphism A B ↔ IsLocalIso A B := by
  constructor
  · intro h
    refine ⟨fun q hqp ↦ ?_⟩
    obtain ⟨g, hg, _⟩ := h q
    have hq : (⟨q, hqp⟩ : PrimeSpectrum B) ∈
        Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hg
    obtain ⟨q', hq'⟩ := hq
    have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away g)))) :=
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))).isOpenEmbedding
        |>.isOpen_range
    obtain ⟨_, ⟨a, rfl⟩, hxa, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_range_self q') hU
    have hb : algebraMap A B a ∉ q := by
      intro hmem
      apply hxa
      have hcomap : q'.asIdeal.comap (algebraMap B (Localization.Away g)) = q :=
        congrArg PrimeSpectrum.asIdeal hq'
      change a ∈ q'.asIdeal.comap (algebraMap A (Localization.Away g))
      rw [IsScalarTower.algebraMap_eq A B (Localization.Away g), ← Ideal.comap_comap, hcomap]
      exact hmem
    refine ⟨g * algebraMap A B a, hqp.mul_notMem hg hb, ?_⟩
    let D := Localization.Away (algebraMap B (Localization.Away g) (algebraMap A B a))
    have : IsLocalization.Away (algebraMap A (Localization.Away g) a) D := by
      rw [IsScalarTower.algebraMap_apply A B (Localization.Away g) a]
      infer_instance
    have : IsStandardOpenImmersion A D :=
      isStandardOpenImmersion_of_isOpenImmersion (C := Localization.Away g) a hsub
    exact .of_algEquiv ((IsLocalization.algEquiv (.powers (g * algebraMap A B a)) D
      (Localization.Away (g * algebraMap A B a))).restrictScalars A)
  · intro h q _
    obtain ⟨g, hg, hstd⟩ := h.exists_notMem_isStandardOpenImmersion q
    obtain ⟨r, _⟩ := IsStandardOpenImmersion.exists_away A (Localization.Away g)
    exact ⟨g, hg, IsOpenImmersion.of_isLocalization r⟩

end Algebra

end
