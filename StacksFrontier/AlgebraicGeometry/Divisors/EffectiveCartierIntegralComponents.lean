module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vanishing ideal of a maximal irreducible piece of the support of an ideal sheaf

Let `X` be a scheme, `I` an ideal sheaf on `X`, and `Z` an irreducible closed subset of the
support of `I` which is maximal among the irreducible closed subsets of that support. Read on an
affine open `Spec A ⊆ X` that `Z` meets, the vanishing ideal of `Z` is a *minimal prime over*
the ideal cut out by `I` on that chart: it is prime because `Z` is irreducible, it contains the
ideal of `I` because `Z` lies in the support, and it is minimal because `Z` is maximal.

Minimality is the geometric content. A prime `P` between the ideal of `I` and the ideal of `Z`
has an irreducible zero locus inside the chart; the closure of its image in `X` is an
irreducible closed subset of the support containing `Z`, because a nonempty open piece of an
irreducible set is dense in it, so maximality of `Z` collapses it back onto `Z` and `P` onto the
vanishing ideal of `Z`.

The intended use is Krull's principal ideal theorem: on a chart where `I` is cut out by a single
nonzerodivisor, minimality bounds the height of the vanishing ideal of `Z` by one.

## Main results

* `Stacks.Divisors.mem_minimalPrimes_ideal_vanishingIdeal` — on an affine open meeting a maximal
  irreducible closed subset `Z` of the support of an ideal sheaf `I`, the vanishing ideal of `Z`
  is a minimal prime over the ideal of `I`.
* `Stacks.Divisors.isPrime_ideal_vanishingIdeal` — the vanishing ideal of an irreducible closed
  set is prime on every affine open that it meets.
* `Stacks.Divisors.subset_closure_inter_of_isIrreducible` — a nonempty open piece of an
  irreducible set is dense in it.

## Implementation notes

Maximality of `Z` inside the support is taken as an explicit hypothesis on closed irreducible
subsets of `X` rather than as membership in `irreducibleComponents` of the support as a
subspace; the two are equivalent, and the explicit form avoids transporting closed sets through
the subtype of the support.

The coercion `(U.2.fromSpec : _ → X)` of the canonical morphism `Spec Γ(X, U) ⟶ X` of an affine
open is ascribed at each use, and the open-immersion instance for it is supplied in term mode.
Mathlib proves the analogous statements about `vanishingIdeal` behind
`backward.isDefEq.respectTransparency`, which is the symptom of that coercion having two
spellings that agree only at default transparency; pinning the spelling removes the need for the
option.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- An irreducible set is contained in the closure of its intersection with any open set that it
meets: a nonempty open piece of an irreducible set is dense in it. -/
@[ega "0 2.1.6" "density of Z ∩ U in Z"]
theorem subset_closure_inter_of_isIrreducible {α : Type*} [TopologicalSpace α] {Z : Set α}
    (hZ : IsIrreducible Z) {V : Set α} (hV : IsOpen V) (hne : (Z ∩ V).Nonempty) :
    Z ⊆ closure (Z ∩ V) := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨y, hyZ, hyV, hyO⟩ := hZ.2 V O hV hO hne ⟨x, hx, hxO⟩
  exact ⟨y, hyO, hyZ, hyV⟩

/-- The canonical morphism from the spectrum of the sections on an affine open is an open
immersion. Supplied in term mode, so that the coercion to a map of topological spaces has a
single spelling. -/
theorem isOpenImmersion_fromSpec (U : X.affineOpens) : IsOpenImmersion U.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

/-- The image under `Spec Γ(X, U) ⟶ X` of the part of a set lying over an affine open `U` is
that set intersected with `U`. -/
theorem fromSpec_image_preimage (U : X.affineOpens) (T : Set X) :
    (U.2.fromSpec : _ → X) '' ((U.2.fromSpec : _ → X) ⁻¹' T) = T ∩ (U.1 : Set X) := by
  have _ := isOpenImmersion_fromSpec U
  have h : Set.range (U.2.fromSpec : _ → X) = (U.1 : Set X) := IsAffineOpen.range_fromSpec U.2
  rw [Set.image_preimage_eq_inter_range, h]

/-- The part of the support of an ideal sheaf lying over an affine open, read in the spectrum of
the ring of sections there, is the zero locus of the ideal on that open. -/
theorem preimage_fromSpec_supportSet (I : X.IdealSheafData) (U : X.affineOpens) :
    (U.2.fromSpec : _ → X) ⁻¹' I.supportSet
      = PrimeSpectrum.zeroLocus (↑(I.ideal U) : Set ↑Γ(X, U.1)) := by
  have _ := isOpenImmersion_fromSpec U
  refine U.2.fromSpec.isOpenEmbedding.injective.image_injective ?_
  have h3 : (U.2.fromSpec : _ → X) '' PrimeSpectrum.zeroLocus (↑(I.ideal U) : Set ↑Γ(X, U.1))
      = X.zeroLocus (↑(I.ideal U) : Set ↑Γ(X, U.1)) ∩ (U.1 : Set X) :=
    IsAffineOpen.fromSpec_image_zeroLocus U.2 _
  rw [fromSpec_image_preimage, h3]
  exact I.coe_support_inter U

/-- The zero locus, on an affine open, of the vanishing ideal of a closed set is the part of
that closed set lying over the open. -/
theorem zeroLocus_ideal_vanishingIdeal (Z : Closeds X) (U : X.affineOpens) :
    PrimeSpectrum.zeroLocus (↑((vanishingIdeal Z).ideal U) : Set ↑Γ(X, U.1))
      = (U.2.fromSpec : _ → X) ⁻¹' (Z : Set X) := by
  have _ := isOpenImmersion_fromSpec U
  rw [vanishingIdeal_ideal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (Z.isClosed.preimage U.2.fromSpec.continuous).closure_eq

/-- The vanishing ideal of a closed set is radical on every affine open. -/
theorem isRadical_ideal_vanishingIdeal (Z : Closeds X) (U : X.affineOpens) :
    ((vanishingIdeal Z).ideal U).IsRadical := by
  rw [vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- On an affine open that it meets, the vanishing ideal of an irreducible closed set is a prime
ideal. -/
theorem isPrime_ideal_vanishingIdeal (Z : Closeds X) (hZ : IsPreirreducible (Z : Set X))
    (U : X.affineOpens) (hne : ((Z : Set X) ∩ (U.1 : Set X)).Nonempty) :
    ((vanishingIdeal Z).ideal U).IsPrime := by
  have _ := isOpenImmersion_fromSpec U
  have hSpre : IsPreirreducible ((U.2.fromSpec : _ → X) ⁻¹' (Z : Set X)) :=
    hZ.preimage U.2.fromSpec.isOpenEmbedding
  have hSne : ((U.2.fromSpec : _ → X) ⁻¹' (Z : Set X)).Nonempty := by
    rwa [← Set.image_nonempty (f := (U.2.fromSpec : _ → X)), fromSpec_image_preimage]
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _
    (isRadical_ideal_vanishingIdeal Z U)).1
    (by rw [zeroLocus_ideal_vanishingIdeal]; exact ⟨hSne, hSpre⟩)

/-- **Minimality.** Let `Z` be an irreducible closed subset of the support of an ideal sheaf `I`
which is maximal among the irreducible closed subsets of that support. On every affine open that
`Z` meets, the vanishing ideal of `Z` is a minimal prime over the ideal of `I`. -/
@[ega "0 16.3.1" "partial"]
theorem mem_minimalPrimes_ideal_vanishingIdeal (I : X.IdealSheafData) (Z : Closeds X)
    (hZirr : IsIrreducible (Z : Set X)) (hZsub : (Z : Set X) ⊆ I.supportSet)
    (hZmax : ∀ T : Set X, IsClosed T → IsIrreducible T → T ⊆ I.supportSet →
      (Z : Set X) ⊆ T → T ⊆ (Z : Set X))
    (U : X.affineOpens) (hne : ((Z : Set X) ∩ (U.1 : Set X)).Nonempty) :
    (vanishingIdeal Z).ideal U ∈ (I.ideal U).minimalPrimes := by
  have _ := isOpenImmersion_fromSpec U
  have hsupp := preimage_fromSpec_supportSet I U
  refine ⟨⟨isPrime_ideal_vanishingIdeal Z hZirr.2 U hne, ?_⟩, ?_⟩
  · rw [vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal, ← hsupp]
    exact Set.preimage_mono hZsub
  · intro P hP hPle
    have hPprime := hP.1
    have hST : (U.2.fromSpec : _ → X) ⁻¹' (Z : Set X)
        ⊆ PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1)) := by
      rw [← zeroLocus_ideal_vanishingIdeal Z U]
      exact PrimeSpectrum.zeroLocus_anti_mono_ideal hPle
    have hT₀irr : IsIrreducible (PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1))) :=
      (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical P hPprime.isRadical).2 hPprime
    have hTirr : IsIrreducible
        (closure ((U.2.fromSpec : _ → X) '' PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1)))) :=
      (hT₀irr.image _ U.2.fromSpec.continuous.continuousOn).closure
    have hTsub : closure ((U.2.fromSpec : _ → X) ''
        PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1))) ⊆ I.supportSet := by
      refine closure_minimal ?_ I.isClosed_supportSet
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p ∈ PrimeSpectrum.zeroLocus (↑(I.ideal U) : Set ↑Γ(X, U.1)) :=
        PrimeSpectrum.zeroLocus_anti_mono_ideal hP.2 hp
      rwa [← hsupp] at hp'
    have hZT : (Z : Set X) ⊆ closure ((U.2.fromSpec : _ → X) ''
        PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1))) := by
      have h1 : (Z : Set X) ∩ (U.1 : Set X)
          ⊆ (U.2.fromSpec : _ → X) '' PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1)) := by
        rw [← fromSpec_image_preimage U (Z : Set X)]
        exact Set.image_mono hST
      exact (subset_closure_inter_of_isIrreducible hZirr U.1.2 hne).trans (closure_mono h1)
    have hTZ := hZmax _ isClosed_closure hTirr hTsub hZT
    calc (vanishingIdeal Z).ideal U
        = PrimeSpectrum.vanishingIdeal ((U.2.fromSpec : _ → X) ⁻¹' (Z : Set X)) :=
          vanishingIdeal_ideal Z U
      _ ≤ PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (↑P : Set ↑Γ(X, U.1))) :=
          PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => hTZ (subset_closure ⟨p, hp, rfl⟩)
      _ = P.radical := PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical P
      _ = P := hPprime.radical

end Stacks.Divisors

end
