module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite locally free modules are the flat modules of finite presentation

A module over a commutative ring is finite locally free, in the sense of a covering family of
elements whose localizations make the module finite free, exactly when it is flat and of finite
presentation.

## Main results

* `Module.isFiniteLocallyFree_iff` is the equivalence.

## Implementation notes

Both implications are local-to-global statements for the covering family. Finite presentation
and flatness are deduced from the localizations by
`Module.FinitePresentation.of_localizationSpan` and `Module.flat_of_localized_span`, using that
a finite free module over a localization is projective and flat over the base. Conversely a flat
module of finite presentation is free over every local ring, and finite presentation spreads
that freeness from a prime to a basic open neighbourhood of it, which produces the covering
family out of the chosen elements.

## References

* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
-/

@[expose] public section

universe u

/-- A module is finite locally free if and only if it is of finite presentation and flat. This is
the commutative-algebra content of [Stacks, Tag 02KB]. -/
theorem Module.isFiniteLocallyFree_iff (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] :
    Module.IsFiniteLocallyFree R M ↔
      Module.FinitePresentation R M ∧ Module.Flat R M := by
  constructor
  · rintro ⟨ι, f, hspan, hfree⟩
    have hfp : Module.FinitePresentation R M := by
      apply Module.FinitePresentation.of_localizationSpan (Set.range f) hspan
      rintro ⟨a, i, rfl⟩
      let : Module.Free (Localization.Away (f i))
          (LocalizedModule (Submonoid.powers (f i)) M) := (hfree i).1
      let : Module.Finite (Localization.Away (f i))
          (LocalizedModule (Submonoid.powers (f i)) M) := (hfree i).2
      exact Module.finitePresentation_of_projective _ _
    have hflat : Module.Flat R M := by
      apply Module.flat_of_localized_span R M (Set.range f) hspan
      rintro ⟨a, i, rfl⟩
      let : Module.Free (Localization.Away (f i))
          (LocalizedModule (Submonoid.powers (f i)) M) := (hfree i).1
      exact Module.Flat.trans R (Localization.Away (f i)) _
    exact ⟨hfp, hflat⟩
  · rintro ⟨hfp, hflat⟩
    let : Module.FinitePresentation R M := hfp
    let : Module.Flat R M := hflat
    have hlocal (p : PrimeSpectrum R) :
        ∃ a : R, a ∉ p.asIdeal ∧
          Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
      let : Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
      obtain ⟨a, ha, hfree, -⟩ :=
        Module.FinitePresentation.exists_free_localizedModule_powers
          p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
          (Localization.AtPrime p.asIdeal)
      exact ⟨a, ha, hfree⟩
    choose f hf hfree using hlocal
    refine ⟨PrimeSpectrum R, f, ?_, fun p ↦ ⟨hfree p, inferInstance⟩⟩
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
    intro p _
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨p, by simpa [PrimeSpectrum.mem_basicOpen] using hf p⟩

end
