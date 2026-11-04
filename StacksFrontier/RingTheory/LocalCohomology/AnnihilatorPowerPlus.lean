module

public import StacksFrontier.RingTheory.LocalCohomology.AnnihilatorPower
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport

/-!
# Annihilating the local cohomology of a complex by a power of the ideal

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and write `Z = V(I)` for its zero locus.
For an object `K` of the bounded-below derived category of `A`-modules, the local cohomology
modules `H^i_Z(K)` are annihilated by some ideal whose zero locus is contained in `Z`, uniformly
for `i ≤ n`, exactly when they are annihilated by a single power `I ^ e`.

The statement is pure ideal theory: `V(J) ⊆ V(I)` says exactly that `I` lies in the radical of
`J`, so a finitely generated `I` has a power inside `J`, and conversely `V(I ^ e) = V(I)` for
`e ≥ 1`. Accordingly no hypothesis on the cohomology of `K` is needed; the ideal-theoretic
content is `Stacks.LocalCohomology.exists_le_iff_exists_pow_le`.

## Main results

* `Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator_plus` — the
  annihilators of the local cohomology of a bounded-below complex are cut out by a power of `I`.

## References

* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- **Stacks 0EI1, equivalence of (2) and (3) for closed support.** For support `V(I)` in a
Noetherian ring, an ideal supported in `V(I)` annihilates the local cohomology of a bounded-below
complex through degree `n` exactly when a single power of `I` does so. -/
theorem exists_annihilator_iff_exists_power_annihilator_plus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (n : ℤ) :
    (∃ J : Ideal A,
      PrimeSpectrum.zeroLocus (J : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
        (localCohomologyWithSupportInPlus.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A)) K i)) ↔
      (∃ e : ℕ, ∀ i : ℤ, i ≤ n → I ^ e ≤ Module.annihilator A
        (localCohomologyWithSupportInPlus.{u, v} A
          (PrimeSpectrum.zeroLocus (I : Set A)) K i)) :=
  exists_le_iff_exists_pow_le A I n fun i ↦ Module.annihilator A
    (localCohomologyWithSupportInPlus.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) K i)

end Stacks.LocalCohomology

end
