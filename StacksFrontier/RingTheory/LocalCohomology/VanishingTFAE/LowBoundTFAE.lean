module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenCriterion
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ZeroLocusGeometry

/-!
# The vanishing equivalence of Tag 0DX7 for a bound at most zero

Let `I` be a finitely generated ideal of a commutative ring `A` and `Y = V(I)` its zero locus in
`Spec A`. [Stacks, Tag 0DX7] asserts, for every `d ≥ -1`, the equivalence of

1. `H^i_Y(A) = 0` for all `i > d`;
2. `H^i_Y(M) = 0` for all `i > d`, for every `A`-module `M`, in any universe;
3. the geometric condition: `Y = ∅` if `d = -1`, `Y` open and closed if `d = 0`, and vanishing of
   the sheaf cohomology `H^n(Spec A \ Y, F)` for every quasi-coherent `F` and every `n ≥ d` if
   `d > 0`.

This file proves that equivalence, **verbatim and in full, for every `d` with `-1 ≤ d ≤ 0`** —
that is, in both of the regimes in which the third condition is a condition on `Y` itself. The
remaining regime `d > 0`, where the third condition is about sheaf cohomology on the complement,
is not reachable here; see the implementation notes.

The three inputs are:

* (1) ⇔ (2) is `Stacks.LocalCohomology.isZero_homology_localCohomology_forall_iff`, the descending
  induction of the source, which holds for every `d`.
* at `d = -1`, (1) ⇔ (3) is
  `Stacks.LocalCohomology.zeroLocus_empty_iff_isZero_localCohomologyModule`.
* at `d = 0`, (1) ⇔ (3) is
  `Stacks.LocalCohomology.isClopen_zeroLocus_iff_isZero_localCohomologyModule`.

## Main results

* `Stacks.LocalCohomology.localCohomology_vanishing_tfae_of_nonpos` — **[Stacks, Tag 0DX7] for
  `-1 ≤ d ≤ 0`.**

## Implementation notes

No `@[stacks 0DX7]` attribute is placed. The tagged statement is the equivalence for an arbitrary
`d ≥ -1`, and the hypothesis `d ≤ 0` is a genuine restriction of it: what is missing is the
comparison

  `H^n(Spec A \ V(I), M̃|U) ≅ H^{n+1}_{V(I)}(M)` for `n ≥ 1`,

which both directions of the `d > 0` clause need and which this library does not have. Its two
halves are both present —
`Stacks.LocalCohomology.homologyComplementIsoLocalCohomologyModule` identifies
`H^n` of the third term of a `Stacks.LocalCohomology.LocalizationTriangleData` with
`H^{n+1}_{V(I)}(M)` in every degree `n ≥ 1`, and
`Stacks.LocalCohomology.homologyDerivedSectionsIsoCechCohomology` identifies the cohomology of
`Stacks.LocalCohomology.derivedSectionsOnAffineComplement` with the Čech cohomology of the
standard covering of the complement — but nothing identifies the third term of a localization
triangle with derived sections on the complement above degree zero, where the `sectionsIso` field
of `Stacks.LocalCohomology.LocalizationTriangleData` stops.

The two clauses at `d ≤ 0` are nevertheless not a weakening of the source's statement at those
values of `d`: the first conjunct of condition (3) is vacuous unless `d = -1`, the second unless
`d = 0`, and the third unless `d > 0`, so at each `d ≤ 0` condition (3) is exactly one of the two
conditions on `Y` and the third conjunct carries no content. It is written out below in the
source's form all the same, so that the statement is the tagged one with `d` restricted and
nothing else changed.

`HasDerivedCategory.standard` is pinned as a local instance, as it is in every file of this
development and as it is in the definition of `Stacks.LocalCohomology.localCohomologyModule`
itself.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-- **[Stacks, Tag 0DX7] for a bound `-1 ≤ d ≤ 0`.** For a finitely generated ideal `I` of a
commutative ring `A` and `-1 ≤ d ≤ 0`, the vanishing of `H^i_{V(I)}(A)` above `d`, the same
vanishing for every `A`-module in any universe, and the geometric condition on `V(I)` and its
complement are equivalent.

(1) ⇔ (2) is the descending induction of the source. At `d = -1` the geometric condition is that
`V(I)` be empty, which is equivalent to (1) because every local cohomology module is `I`-power
torsion, hence supported in `V(I)`, while `H^0_{V(I)}(A/I) = A/I`. At `d = 0` it is that `V(I)` be
open and closed: a clopen is cut out by an idempotent, for which the Čech model of local
cohomology is a two-term surjection, and conversely the vanishing makes the `I`-power-torsion
submodule of `A` surject onto `A/I`, which produces the idempotent. The third conjunct of the
geometric condition is vacuous because `d ≤ 0`. -/
theorem localCohomology_vanishing_tfae_of_nonpos
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (d : ℤ) (_hd : (-1 : ℤ) ≤ d) (hd' : d ≤ 0) :
    List.TFAE [
      ∀ (i : ℤ), d < i →
        IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i),
      ∀ (M : ModuleCat.{max u v} A) (i : ℤ), d < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
            ((Dualizing.localCohomologyFunctor A I hI).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))),
      ((d = -1 → PrimeSpectrum.zeroLocus (I : Set A) = ∅) ∧
        (d = 0 → IsClopen (PrimeSpectrum.zeroLocus (I : Set A))) ∧
        (0 < d →
          let U : (Spec (CommRingCat.of A)).Opens :=
            ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
              (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩
          ∀ (F : (U : Scheme).Modules),
            F.IsQuasicoherent → ∀ (n : ℕ), d ≤ (n : ℤ) →
              IsZero (Hgroup (U : Scheme).ringCatSheaf ⊤ n F)))] := by
  tfae_have 1 → 2 := fun h₁ M i hi =>
    isZero_homology_localCohomology_of_isZero_homology_self.{v} I hI d h₁ M i hi
  tfae_have 2 → 1 := fun h₂ => (isZero_homology_localCohomology_forall_iff.{v} I hI d).2 h₂
  tfae_have 1 → 3 := by
    intro h₁
    refine ⟨fun hneg => ?_, fun hzero => ?_, fun hpos => absurd hpos (by omega)⟩
    · subst hneg
      exact zeroLocus_empty_of_isZero_localCohomologyModule A I hI h₁
    · subst hzero
      exact isClopen_zeroLocus_of_isZero_localCohomologyModule I hI h₁
  tfae_have 3 → 1 := by
    rintro ⟨hneg, hzero, -⟩
    rcases lt_or_eq_of_le hd' with hlt | rfl
    · have hdneg : d = -1 := by omega
      subst hdneg
      exact fun i _ => isZero_localCohomologyModule_of_zeroLocus_empty A I hI (hneg rfl) _ i
    · exact (isClopen_zeroLocus_iff_isZero_localCohomologyModule I hI).2 (hzero rfl)
  tfae_finish

end Stacks.LocalCohomology

end
