module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison

/-!
# Local cohomology killed by a power of an element, from a bound off its zero locus

Let `A` be a Noetherian algebra of finite type over a field, `M` a finite `A`-module, `I` a
finitely generated ideal and `f ∈ I`. Suppose that for every prime `𝔭` with `f ∉ 𝔭` and every
`𝔮 ⊇ 𝔭` in `V(I)` one has

`depth(M_𝔭) + dim((A/𝔭)_𝔮) > s`.

Then a single power of `f` kills `H^i_I(M)` for every `i ≤ s`.

This is how Faltings' annihilator theorem [Stacks, Tag 0EFC] is used in the proof of
[Stacks, Tag 0EL1]. The theorem is applied with the two closed sets `T = V(I)` and `T' = V(f)`.
`T ⊆ T'` holds because `f` vanishes on `V(I)`, and both sets are closed, hence stable under
specialization. The annihilating ideal `J` it produces satisfies `V(J) ⊆ V(f)`, so `f` lies in
the radical of `J` and some power of `f` lies in `J`.

The bound is required only at primes `𝔭` *outside* `V(f)`, that is, at points of the punctured
cone lying off the zero scheme of the section. That is exactly the source's hypothesis: it is
imposed on `X ∖ Y` and nowhere else.

## Main results

* `Stacks.Algebraization.SectionRingCone.exists_pow_smul_localCohomologyModule_eq_zero_of_depth`
  — the power of `f` killing `H^i_I(M)` for every `i ≤ s`, in the coreflection model
  `Stacks.LocalCohomology.localCohomologyModule`.

## References

* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Algebraization.SectionRingCone

/-- **A power of `f` kills the local cohomology of `M` in degrees `≤ s`**, as soon as
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > s` for every prime `𝔭` not containing `f` and every `𝔮 ⊇ 𝔭` in
`V(I)`.

Faltings' annihilator theorem [Stacks, Tag 0EFC] is applied with supports `V(I) ⊆ V(f)`. Its
annihilating ideal `J` has `V(J) ⊆ V(f)`, so some `f ^ c` lies in `J`. The two models of local
cohomology are compared by
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`. -/
theorem exists_pow_smul_localCohomologyModule_eq_zero_of_depth
    (k : Type u) [Field k] (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (hI : I.FG) (f : A)
    (hIf : PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus ({f} : Set A)) (s : ℕ)
    (hdepth : ∀ p q : PrimeSpectrum A, f ∉ p.asIdeal →
      q ∈ PrimeSpectrum.zeroLocus (I : Set A) → p.asIdeal ≤ q.asIdeal →
        depthAddRelativeDim A M p q > ((s : ℤ) : EInt)) :
    ∃ c : ℕ, ∀ j : ℤ, j ≤ (s : ℤ) →
      ∀ x : Stacks.LocalCohomology.localCohomologyModule A I hI (ModuleCat.of A M) j,
        f ^ c • x = 0 := by
  obtain ⟨omega, homega⟩ := exists_isDualizingComplex_of_finiteType_field k A
  have hTT' := hIf
  have hT : StableUnderSpecialization (PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  have hT' : StableUnderSpecialization (PrimeSpectrum.zeroLocus ({f} : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  obtain ⟨J, hJT', hJann⟩ :=
    (Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff A M
      (PrimeSpectrum.zeroLocus (I : Set A)) (PrimeSpectrum.zeroLocus ({f} : Set A)) hTT' hT hT'
      (s : ℤ) (Int.natCast_nonneg s) omega homega).mpr
      (fun p q hp hq hpq => hdepth p q
        (fun hfp => hp (by simpa [PrimeSpectrum.mem_zeroLocus] using hfp)) hq hpq)
  have hsub : PrimeSpectrum.zeroLocus (J : Set A)
      ⊆ PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal A) : Set A) := by
    rw [PrimeSpectrum.zeroLocus_span]
    exact hJT'
  obtain ⟨c, hc⟩ : f ∈ J.radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J (Ideal.span {f})).mp hsub
      (Ideal.mem_span_singleton_self f)
  refine ⟨c, fun j hj x => ?_⟩
  have e := Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule
    A I hI (ModuleCat.of A M) j
  have hx := Module.mem_annihilator.mp (hJann j hj hc) (e.inv x)
  simpa only [map_smul, map_zero, ← ConcreteCategory.comp_apply, e.inv_hom_id,
    ConcreteCategory.id_apply] using congrArg (fun y => e.hom y) hx

end Stacks.Algebraization.SectionRingCone

end
