module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.RingTheory.Spectrum.Prime.CodimensionHeight
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A codimension bound on a scheme, read on an affine open

A hypothesis of the form "every irreducible closed subset of `X` contained in the closed set `Z`
has codimension at least `e`" is a statement about the topology of `X`. The commutative algebra
that consumes it works on an affine open `U` of `X` and asks for a bound on the heights of the
minimal primes of an ideal `I ⊆ Γ(U, ⊤)` whose zero locus lands in `Z`. This module performs
that translation once.

## Main results

* `AlgebraicGeometry.Scheme.le_height_of_mem_minimalPrimes_of_isAffineOpen`: the translation.
* `AlgebraicGeometry.Scheme.exists_mem_minimalPrimes_height_eq_of_isAffineOpen`: the *exact*
  translation, for a single pinned irreducible component. A hypothesis of the form "`Z` is an
  irreducible component of the closed set `C` and `codim(Z, X) = e`" becomes, on an affine open
  meeting `Z`, the datum `∃ p ∈ I.minimalPrimes, height p = e` for any ideal `I` whose zero locus
  is `C` on the chart. This is what a dimension count asking for one component of the right
  codimension consumes; the inequality above is not enough for it, and conversely a bound on
  *every* irreducible closed subset is not available from a hypothesis about one component.
* `AlgebraicGeometry.Scheme.isPrime_nilradical_of_isAffine`: the ring of an irreducible affine
  scheme has prime nilradical, so its reduction is a domain.

## Implementation notes

The open immersion used is `U.toScheme.isoSpec.inv ≫ U.ι : Spec Γ(U, ⊤) ⟶ X`, so that the ring
is `Γ(U.toScheme, ⊤)` — the ring in which the local equations of a subscheme over `U` naturally
live — rather than `Γ(X, U)`, which would need the comparison `Scheme.Opens.topIso`. The two
ingredients are `AlgebraicGeometry.Scheme.isoSpec_inv_image_zeroLocus`, which identifies the
image of a prime-spectrum zero locus with the scheme-theoretic one, and
`PrimeSpectrum.le_height_of_mem_minimalPrimes_of_isOpenEmbedding`, which is the bound itself.

## References

* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The image of a prime-spectrum zero locus in `X`, along `Spec Γ(U, ⊤) ⟶ X`, is the
scheme-theoretic one, so it lies in `Z` whenever that does. -/
private theorem image_zeroLocus_subset_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    [IsAffine U.toScheme] {Z : Set X} {I : Ideal Γ(U.toScheme, ⊤)}
    (hI : U.ι.base '' U.toScheme.zeroLocus (U := ⊤) (I : Set Γ(U.toScheme, ⊤)) ⊆ Z) :
    (U.toScheme.isoSpec.inv ≫ U.ι).base ''
      PrimeSpectrum.zeroLocus (I : Set Γ(U.toScheme, ⊤)) ⊆ Z := by
  rintro _ ⟨p, hp, rfl⟩
  refine hI ⟨U.toScheme.isoSpec.inv.base p, ?_, rfl⟩
  rw [← Scheme.isoSpec_inv_image_zeroLocus (X := U.toScheme) (I : Set Γ(U.toScheme, ⊤))]
  exact ⟨p, hp, rfl⟩

/-- **A codimension bound on a scheme, read on the minimal primes over an affine open.** Let `Z`
be a closed subset of a scheme `X` every irreducible closed subset of which has codimension at
least `e`, let `U` be an affine open of `X` and let `I` be an ideal of `Γ(U, ⊤)` whose zero locus
lies in `Z`. Then every minimal prime over `I` has height at least `e`.

The irreducible closed subsets of `Spec Γ(U, ⊤)` cut out by the minimal primes over `I` are
carried by the open immersion `Spec Γ(U, ⊤) ⟶ X` to irreducible closed subsets of `X` contained
in `Z`, and codimension is unchanged by an open immersion ([Stacks, Tag 02I4]). -/
theorem le_height_of_mem_minimalPrimes_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    [IsAffine U.toScheme] {Z : Set X} (hZ : IsClosed Z) {e : ℕ∞}
    (hcodim : ∀ Y : IrreducibleCloseds X, (Y : Set X) ⊆ Z → e ≤ codimension Y)
    {I : Ideal Γ(U.toScheme, ⊤)}
    (hI : U.ι.base '' U.toScheme.zeroLocus (U := ⊤) (I : Set Γ(U.toScheme, ⊤)) ⊆ Z)
    {q : Ideal Γ(U.toScheme, ⊤)} (hq : q ∈ I.minimalPrimes) :
    e ≤ q.height := by
  exact PrimeSpectrum.le_height_of_mem_minimalPrimes_of_isOpenEmbedding
    (Scheme.Hom.isOpenEmbedding (U.toScheme.isoSpec.inv ≫ U.ι)) hZ hcodim
    (image_zeroLocus_subset_of_isAffineOpen U hI) hq

/-- **An exact codimension on a scheme, read as an exact height on an affine open.** Let `C` be a
closed subset of a scheme `X`, let `Z` be an irreducible component of `C` — maximal among the
irreducible closed subsets of `X` contained in `C` — let `U` be an affine open meeting `Z`, and
let `I` be an ideal of `Γ(U, ⊤)` whose zero locus lies in `C` and which vanishes on the trace of
`Z`. Then some minimal prime over `I` has height exactly `codim(Z, X)`.

The prime is the one cutting out `Z ∩ U`: it is minimal over `I` because `Z` is maximal
(`PrimeSpectrum.vanishingIdeal_preimage_mem_minimalPrimes`) and its height is `codim(Z, X)` by
[Stacks, Tag 02I4] (`PrimeSpectrum.height_vanishingIdeal_preimage`). -/
theorem exists_mem_minimalPrimes_height_eq_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    [IsAffine U.toScheme] {C : Set X} (hC : IsClosed C) {Z : IrreducibleCloseds X}
    (hmax : Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆ C) Z)
    (hne : ((U : Set X) ∩ (Z : Set X)).Nonempty)
    {I : Ideal Γ(U.toScheme, ⊤)}
    (hIC : U.ι.base '' U.toScheme.zeroLocus (U := ⊤) (I : Set Γ(U.toScheme, ⊤)) ⊆ C)
    (hIZ : U.ι.base ⁻¹' (Z : Set X) ⊆
      U.toScheme.zeroLocus (U := ⊤) (I : Set Γ(U.toScheme, ⊤))) :
    ∃ p : Ideal Γ(U.toScheme, ⊤), p ∈ I.minimalPrimes ∧ p.height = codimension Z := by
  set f := (U.toScheme.isoSpec.inv ≫ U.ι).base with hfdef
  have hf : Topology.IsOpenEmbedding f :=
    Scheme.Hom.isOpenEmbedding (U.toScheme.isoSpec.inv ≫ U.ι)
  have hfZ : f ⁻¹' (Z : Set X) ⊆ PrimeSpectrum.zeroLocus (I : Set Γ(U.toScheme, ⊤)) := by
    rw [← Scheme.isoSpec_inv_preimage_zeroLocus (X := U.toScheme) (I : Set Γ(U.toScheme, ⊤))]
    exact fun p hp => hIZ hp
  have hne' : (f ⁻¹' (Z : Set X)).Nonempty := by
    obtain ⟨x, hxU, hxZ⟩ := hne
    rw [← Scheme.Opens.range_ι] at hxU
    obtain ⟨y, hy⟩ := hxU
    obtain ⟨p, hp⟩ := (Scheme.homeoOfIso U.toScheme.isoSpec.symm).surjective y
    have hfp : f p = x := by
      show U.ι.base (U.toScheme.isoSpec.inv.base p) = x
      rw [show U.toScheme.isoSpec.inv.base p = y from hp, hy]
    exact ⟨p, by rw [Set.mem_preimage, hfp]; exact hxZ⟩
  exact ⟨PrimeSpectrum.vanishingIdeal (f ⁻¹' (Z : Set X)),
    PrimeSpectrum.vanishingIdeal_preimage_mem_minimalPrimes hf Z hne' hC hmax
      (image_zeroLocus_subset_of_isAffineOpen U hIC) hfZ,
    PrimeSpectrum.height_vanishingIdeal_preimage hf Z hne'⟩

/-- **The nilradical of the ring of an irreducible affine scheme is prime.** An affine scheme is
homeomorphic to the spectrum of its ring of functions, and the spectrum of a ring is irreducible
exactly when its nilradical is prime
(`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`).

This is the hypothesis under which a reduction argument may replace the ring of an affine open by
a domain: the quotient `Γ(X, ⊤) / √0` is then a domain with the same spectrum. -/
@[ega "I 1.1.13" "necessity"]
theorem isPrime_nilradical_of_isAffine (X : Scheme.{u}) [IsAffine X] [IrreducibleSpace X] :
    (nilradical Γ(X, ⊤)).IsPrime := by
  rw [← PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  have h : IrreducibleSpace (Spec Γ(X, ⊤)) :=
    (Scheme.homeoOfIso X.isoSpec).irreducibleSpace_iff.mp inferInstance
  convert! h

end AlgebraicGeometry.Scheme

end
