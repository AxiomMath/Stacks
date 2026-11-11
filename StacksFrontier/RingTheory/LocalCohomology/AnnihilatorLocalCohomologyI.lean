module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport

/-!
# Annihilators of local cohomology, I

Let `I` be an ideal of a Noetherian ring `A` admitting a dualizing complex, let `M` be a finite
`A`-module and let `p` be a prime outside `V(I)`. If the depth-plus-dimension inequality
`depth_{A_{p'}}(M_{p'}) + dim((A/p')_q) > s` holds for every prime `p' ⊆ p` and every `q ∈ V(I)`
with `p' ⊆ q`, then a single element of `A` outside `p` annihilates `H^i_{V(I)}(M)` for all
`i ≤ s`.

## Main results

* `Stacks.LocalCohomology.exists_notMem_and_mem_annihilator_localCohomologyWithSupportIn` —
  the deduction of Tag 0EFE from Faltings' annihilator theorem, Tag 0EFC.

## Implementation notes

Faltings' annihilator theorem, Tag 0EFC, is
`Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff`, proved in
`StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator`; here it enters as the argument
`hFaltings`, whose type is that statement quantified over the two supports, the degree and the
dualizing complex. Discharging it gives
`Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyWithSupportIn_of_dualizing`,
which carries Tag 0EFE.

The set `T'` of the source, the union of the `V(f)` over `f ∉ p`, is exactly the set of primes
not contained in `p`. An ideal whose zero locus lies in `T'` is therefore not contained in `p`,
so any of its elements outside `p` annihilates already, with no passage to a power.

## References

* [Stacks Project, Tag 0EFE](https://stacks.math.columbia.edu/tag/0EFE)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **The deduction of Stacks 0EFE from Stacks 0EFC.** For `M` finite over a Noetherian ring `A` with a dualizing complex and `p`
a prime outside `V(I)`, if `depth_{A_{p'}}(M_{p'}) + dim((A/p')_q) > s` for all primes `p' ⊆ p`
and all `q ∈ V(I)` with `p' ⊆ q`, then some `f ∈ A` outside `p` annihilates `H^i_{V(I)}(M)`
for every `i ≤ s`. -/
public theorem exists_notMem_and_mem_annihilator_localCohomologyWithSupportIn
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (p : PrimeSpectrum A) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hFaltings : ∀ (T T' : Set (PrimeSpectrum A)), T ⊆ T' →
      StableUnderSpecialization T → StableUnderSpecialization T' →
      ∀ (s₀ : ℤ), 0 ≤ s₀ →
      ∀ (ω : DerivedCategory (ModuleCat.{u} A)),
        Dualizing.IsDualizingComplex (A := A) (K := ω) →
        ((∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
            ∀ i : ℤ, i ≤ s₀ → J ≤ Module.annihilator A
              (localCohomologyWithSupportIn.{u, u} A T
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A M)) i)) ↔
          (∀ x y : PrimeSpectrum A, x ∉ T' → y ∈ T → x.asIdeal ≤ y.asIdeal →
            Stacks.Algebraization.enatToEInt
                (Module.depth (Localization.AtPrime x.asIdeal)
                  (maximalIdeal (Localization.AtPrime x.asIdeal))
                  (LocalizedModule x.asIdeal.primeCompl M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
                  x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) > (s₀ : EInt))))
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (I : Set A) → x.asIdeal ≤ y.asIdeal →
      Stacks.Algebraization.enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) > (s : EInt)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  have hT : StableUnderSpecialization (PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization
  have hT' : StableUnderSpecialization {x : PrimeSpectrum A | ¬ x.asIdeal ≤ p.asIdeal} := by
    intro x y hxy hx hy
    exact hx (((PrimeSpectrum.asIdeal_le_asIdeal x y).2
      ((PrimeSpectrum.le_iff_specializes x y).2 hxy)).trans hy)
  have hTT' : PrimeSpectrum.zeroLocus (I : Set A) ⊆
      {x : PrimeSpectrum A | ¬ x.asIdeal ≤ p.asIdeal} := by
    intro y hy hyp
    rw [PrimeSpectrum.mem_zeroLocus] at hy
    exact hp ((PrimeSpectrum.mem_zeroLocus _ _).2 (hy.trans hyp))
  obtain ⟨J, hJT', hJ⟩ :=
    (hFaltings (PrimeSpectrum.zeroLocus (I : Set A))
        {x : PrimeSpectrum A | ¬ x.asIdeal ≤ p.asIdeal} hTT' hT hT' s hs omega homega).mpr
      fun x y hx hy hxy => hdepth x y (not_not.1 hx) hy hxy
  have hJp : ¬ (J : Set A) ⊆ (p.asIdeal : Set A) := fun hsub =>
    hJT' ((PrimeSpectrum.mem_zeroLocus _ _).2 hsub) le_rfl
  obtain ⟨f, hfJ, hfp⟩ := Set.not_subset.1 hJp
  exact ⟨f, hfp, fun i hi => hJ i hi hfJ⟩

end Stacks.LocalCohomology

end
