module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.RingTheory.Depth.FlatModule
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth at a prime of a module which is locally free away from an element

Let `A` be a Noetherian ring, `M` a finite `A`-module and `f ∈ A`. If the localization `M_f` is a
finite locally free `A_f`-module, then `M_𝔭` is a free `A_𝔭`-module for every prime `𝔭` with
`f ∉ 𝔭`, and therefore

`depth_𝔪(A_𝔭) ≤ depth_𝔪(M_𝔭)`

at each such prime, by `Module.depth_le_depth_of_flat`.

The passage from `M_f` to `M_𝔭` is Mathlib's free locus: a finite module over a Noetherian ring
is finitely presented, and for a finitely presented module
`Module.basicOpen_subset_freeLocus_iff` says that `D(f)` lies in the free locus exactly when
`M_f` is a projective `A_f`-module — which is one half of finite local freeness by
`Module.isFiniteLocallyFree_iff_finite_projective`.

This is the input which lets Faltings' annihilator theorem (Stacks 0EFC) be applied to a module
that is locally free on `Spec(A) ∖ V(f)` once the depth–dimension inequality is known for the
ring itself: the inequality for `A` is transported to the inequality for `M` prime by prime.

## Main results

* `Module.free_localizedModule_of_isFiniteLocallyFree_away` — freeness of `M_𝔭` for `f ∉ 𝔭`.
* `Module.depth_localizedModule_le_of_isFiniteLocallyFree_away` — the depth inequality.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Module

/-- **A module which is finite locally free away from `f` is free at every prime avoiding `f`.**
-/
public theorem free_localizedModule_of_isFiniteLocallyFree_away {A : Type u} [CommRing A]
    [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (hf : Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M))
    (p : PrimeSpectrum A) (hp : f ∉ p.asIdeal) :
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) := by
  have _ : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have hproj : Module.Projective (Localization.Away f) (LocalizedModule.Away f M) :=
    ((Module.isFiniteLocallyFree_iff_finite_projective (Localization.Away f)
      (LocalizedModule.Away f M)).1 hf).2
  have hsub : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ⊆ Module.freeLocus A M :=
    Module.basicOpen_subset_freeLocus_iff.mpr hproj
  exact hsub ((PrimeSpectrum.mem_basicOpen f p).2 hp)

/-- **The depth of `M_𝔭` is at least the depth of `A_𝔭`** whenever `M` is finite locally free
away from an element not in `𝔭`. -/
@[sga "2 X 2.1" "partial"]
public theorem depth_localizedModule_le_of_isFiniteLocallyFree_away {A : Type u} [CommRing A]
    [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (hf : Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M))
    (p : PrimeSpectrum A) (hp : f ∉ p.asIdeal) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl A) ≤
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := by
  have _ : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.free_localizedModule_of_isFiniteLocallyFree_away M f hf p hp
  have _ : Module.Flat (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := Module.Flat.of_free
  exact Module.depth_le_depth_of_flat
    (maximalIdeal (Localization.AtPrime p.asIdeal))
    (LocalizedModule p.asIdeal.primeCompl M)

end Module

end
