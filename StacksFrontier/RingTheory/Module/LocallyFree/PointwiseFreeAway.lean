module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite local freeness of a localization from freeness at the primes it sees

Let `A` be a Noetherian ring, `M` a finite `A`-module and `g ∈ A`.  If `M_𝔭` is a free
`A_𝔭`-module for *every* prime `𝔭` with `g ∉ 𝔭`, then `M_g` is a finite locally free
`A_g`-module.

The primes `𝔭` with `g ∉ 𝔭` are exactly the points of the basic open `D(g)`, so the hypothesis
says precisely that `D(g)` is contained in the free locus of `M`.  A finite module over a
Noetherian ring is finitely presented, and for a finitely presented module Mathlib's
`Module.basicOpen_subset_freeLocus_iff` converts that containment into projectivity of `M_g`
over `A_g`; finiteness of `M_g` is automatic, and
`Module.isFiniteLocallyFree_iff_finite_projective` assembles the two into finite local
freeness.

This is the converse of `Module.free_localizedModule_of_isFiniteLocallyFree_away`, and the two
together say that for a finite module over a Noetherian ring, finite local freeness of `M_g`
over `A_g` is a pointwise condition on `D(g)`.

## Main results

* `Module.isFiniteLocallyFree_away_of_free_localizedModule_atPrime` — freeness of `M_𝔭` at every
  prime `𝔭` avoiding `g` implies `Module.IsFiniteLocallyFree A_g M_g`.

## References

* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

universe u

namespace Module

/-- **A finite module over a Noetherian ring which is free at every prime avoiding `g` is
finite locally free after inverting `g`.**

The primes `𝔮` with `g ∉ 𝔮` are the points of the basic open `D(g)`, so the hypothesis states
that `D(g)` lies in the free locus of `M`; for the finitely presented module `M` this is
equivalent to projectivity of `M_g` over `A_g`, which together with the automatic finiteness of
`M_g` is finite local freeness. -/
public theorem isFiniteLocallyFree_away_of_free_localizedModule_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (g : R)
    (h : ∀ (q : Ideal R) [q.IsPrime], g ∉ q →
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) :
    Module.IsFiniteLocallyFree (Localization.Away g) (LocalizedModule.Away g M) := by
  have _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have hsub : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R M :=
    fun p hp => Module.mem_freeLocus.2
      (h p.asIdeal ((PrimeSpectrum.mem_basicOpen g p).1 hp))
  exact (Module.isFiniteLocallyFree_iff_finite_projective (Localization.Away g)
    (LocalizedModule.Away g M)).2
      ⟨inferInstance, Module.basicOpen_subset_freeLocus_iff.1 hsub⟩

end Module

end
