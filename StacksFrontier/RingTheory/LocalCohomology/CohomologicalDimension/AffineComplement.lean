module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.MaximalIdeal
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE

/-!
# The complement of the vanishing locus of an ideal of cohomological dimension one

Let `I` be a finitely generated ideal of a commutative ring `A` and let `Y = V(I)` be its zero
locus in `X = Spec A`. If the cohomological dimension `cd(A, I)` of Stacks 0DX8 equals `1`, then
`U = X ∖ Y` is a nonempty affine open.

Nonemptiness is proved here, and it needs nothing beyond the definition of the cohomological
dimension: were `U` empty, the zero locus of `I` would be the whole spectrum, hence also the zero
locus of the zero ideal, which is cut out by the *empty* family of elements; the generator bound
of Stacks 0DX9 (2) then forces `cd(A, I) ≤ 0`. The argument never uses `cd(A, I) = 1`, only
`cd(A, I) > 0`, and that is how the statement below is phrased, with the formulation of Stacks
0DXD recorded as a corollary.

Affineness is proved too, as a consequence of Serre's criterion (Stacks 01XF) applied to the
quasi-compact open `U` together with the `d = 1` instance of the vanishing equivalence of
Stacks 0DX7 (`Stacks.LocalCohomology.localCohomology_vanishing_tfae_of_one_le`), which turns
`H^i_Y(A) = 0` for `i > 1` into the vanishing of `H^n(U, F)` for every quasi-coherent `F` on `U`
and every `n ≥ 1`.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_nonpos_of_zeroLocus_eq_univ` — an ideal whose
  zero locus is the whole spectrum has cohomological dimension at most `0`.
* `Stacks.LocalCohomology.nonempty_compl_zeroLocus_of_cohomologicalDimension_pos` — positive
  cohomological dimension forces the complement of the zero locus to be nonempty.
* `Stacks.LocalCohomology.nonempty_compl_zeroLocus_of_cohomologicalDimension_eq_one` —
  **Stacks 0DXD**, nonemptiness of the complement in cohomological dimension one.
* `Stacks.LocalCohomology.isCompact_compl_zeroLocus` and
  `Stacks.LocalCohomology.compactSpace_complZeroLocusOpen` — the complement is quasi-compact,
  which is the hypothesis under which Serre's criterion is applied.
* `Stacks.LocalCohomology.isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one` —
  **Stacks 0DXD**, affineness of the complement in cohomological dimension one.
* `nonempty_and_isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one` (in the namespace
  `Stacks.LocalCohomology`) — **Stacks 0DXD** as the source states it: in cohomological dimension
  one the open subscheme `Spec A ∖ V(I)` is nonempty *and* affine, both conjuncts asserted of that
  one object.

## Implementation notes

The affineness half of Stacks 0DXD is assembled from three results, each proved elsewhere in
this development:

* Stacks 01XF, Serre's criterion for affineness, proved as
  `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal` in
  `StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion`: a quasi-compact
  scheme on which the first cohomology of every quasi-coherent ideal sheaf vanishes is affine.
* The `d ≥ 1` regime of Stacks 0DX7, proved as
  `Stacks.LocalCohomology.isZero_hgroup_complement_of_isZero_localCohomologyModule_self` in
  `StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE`: `H^i_Y(A) = 0` for
  `i > d` with `d ≥ 1` forces the vanishing of `H^n(U, F)` for every quasi-coherent `F` on
  `U = Spec A ∖ Y` and every `n ≥ d`. Taking `d = 1` and `n = 1` supplies exactly the `H¹`
  vanishing Serre's criterion asks for on every quasi-coherent ideal sheaf of `U`.
* The quasi-compactness of `U`, proved below as
  `Stacks.LocalCohomology.compactSpace_complZeroLocusOpen`.

The vanishing in module form (`Hgroup`) is converted to the right-derived-functor form Serre's
criterion is stated with by
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`.

The complement is handled as a subset of `PrimeSpectrum A` and, where a scheme is wanted, as the
open subscheme `complZeroLocusOpen` of `Spec A`. This agrees definitionally with
`Stacks.LocalCohomology.complementZeroLocus`, the name the Stacks 0DX7 development uses for the
same open subscheme, so the two interface without any bridging lemma. The carrier of `Spec A`
and `PrimeSpectrum A` are the same topological space but not the same expression, so the passage
between the two quasi-compactness statements is a `change`.

## References

* [Stacks Project, Tag 0DXD](https://stacks.math.columbia.edu/tag/0DXD)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- An ideal whose zero locus is the whole prime spectrum has cohomological dimension at most
`0`. The zero ideal has the same zero locus and is generated by the empty family, so the bound
of Stacks 0DX9 (2) applies with no generators. -/
theorem cohomologicalDimension_nonpos_of_zeroLocus_eq_univ
    (h : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ) :
    cohomologicalDimension A I hI ≤ 0 := by
  have hbound := cohomologicalDimension_le_card_zeroLocus_generators A I hI
    (n := 0) (Fin.elim0 : Fin 0 → A) (by simp [h])
  simpa using hbound

/-- If the cohomological dimension of a finitely generated ideal is positive, the complement of
its zero locus in the prime spectrum is nonempty: an empty complement makes the zero locus the
whole spectrum, which caps the cohomological dimension at `0`. -/
theorem nonempty_compl_zeroLocus_of_cohomologicalDimension_pos
    (hcd : 0 < cohomologicalDimension A I hI) :
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ.Nonempty := by
  rw [Set.nonempty_compl]
  intro h
  exact absurd (cohomologicalDimension_nonpos_of_zeroLocus_eq_univ A I hI h) (by omega)

/-- **Stacks Project, Tag 0DXD.** If a finitely generated ideal has cohomological dimension one,
the complement of its zero locus in the prime spectrum is nonempty. -/
@[stacks 0DXD "nonemptiness"]
theorem nonempty_compl_zeroLocus_of_cohomologicalDimension_eq_one
    (hcd : cohomologicalDimension A I hI = 1) :
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ.Nonempty :=
  nonempty_compl_zeroLocus_of_cohomologicalDimension_pos A I hI (by omega)

include hI in
/-- The complement of the zero locus of a finitely generated ideal is quasi-compact: a subset of
a prime spectrum is quasi-compact and open exactly when it is such a complement. -/
@[ega "I 1.1.10" "more general"]
theorem isCompact_compl_zeroLocus :
    IsCompact (PrimeSpectrum.zeroLocus (I : Set A))ᶜ :=
  (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨I, hI, rfl⟩).1

/-- The complement of the zero locus of an ideal, as an open subscheme of `Spec A`. -/
def complZeroLocusOpen : (Spec (CommRingCat.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩

include hI in
/-- For a finitely generated ideal the open subscheme `Spec A ∖ V(I)` is quasi-compact. This is
the quasi-compactness hypothesis of Serre's criterion for affineness, Stacks 01XF, that
`isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one` below feeds it. -/
theorem compactSpace_complZeroLocusOpen : CompactSpace (complZeroLocusOpen A I).toScheme := by
  have h : IsCompact ((complZeroLocusOpen A I).1 : Set (Spec (CommRingCat.of A))) := by
    show @IsCompact (PrimeSpectrum A) PrimeSpectrum.zariskiTopology
      (PrimeSpectrum.zeroLocus (I : Set A))ᶜ
    exact isCompact_compl_zeroLocus A I hI
  exact isCompact_iff_compactSpace.mp h

/-- **Stacks Project, Tag 0DXD.** If a finitely generated ideal has cohomological dimension one,
the complement of its zero locus, as an open subscheme of `Spec A`, is affine.

Serre's criterion for affineness (Stacks 01XF) applies to the complement
`U = complZeroLocusOpen A I`: it is quasi-compact by `compactSpace_complZeroLocusOpen`, and the
`d = 1` instance of Stacks 0DX7
(`isZero_hgroup_complement_of_isZero_localCohomologyModule_self`) turns the vanishing of
`H^i_{V(I)}(A)` for `i > 1`, which is what cohomological dimension one means, into the vanishing
of `H¹(U, F)` for every quasi-coherent `F` on `U`, in particular for every quasi-coherent ideal
sheaf. -/
@[stacks 0DXD "affineness"]
theorem isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one
    (hcd : cohomologicalDimension A I hI = 1) :
    IsAffine (complZeroLocusOpen A I).toScheme := by
  have hcompact : CompactSpace (complZeroLocusOpen A I).toScheme :=
    compactSpace_complZeroLocusOpen A I hI
  have hbound : IsLocalCohomologyBound A I hI 1 :=
    hcd ▸ isLocalCohomologyBound_cohomologicalDimension A I hI
  have hvan := isZero_hgroup_complement_of_isZero_localCohomologyModule_self A I hI 1 le_rfl
    hbound.2
  refine Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal
    (complZeroLocusOpen A I).toScheme (fun J hJ => ?_)
  exact (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    (complZeroLocusOpen A I).toScheme.ringCatSheaf ⊤ 1 _).2
    (hvan (Subobject.underlying.obj J) hJ 1 le_rfl)

/-- **Stacks Project, Tag 0DXD.** Let `I` be a finitely generated ideal of a commutative ring
`A`. If the cohomological dimension `cd(A, I)` equals `1`, then `Spec A ∖ V(I)` is a nonempty
affine scheme.

This is the source statement, both of its assertions made about the single open subscheme
`complZeroLocusOpen A I = Spec A ∖ V(I)`: nonemptiness from
`nonempty_compl_zeroLocus_of_cohomologicalDimension_eq_one` and affineness from
`isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one`. -/
@[stacks 0DXD]
theorem nonempty_and_isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one
    (hcd : cohomologicalDimension A I hI = 1) :
    Nonempty (complZeroLocusOpen A I).toScheme ∧
      IsAffine (complZeroLocusOpen A I).toScheme := by
  obtain ⟨x, hx⟩ := nonempty_compl_zeroLocus_of_cohomologicalDimension_eq_one A I hI hcd
  exact ⟨⟨⟨x, hx⟩⟩, isAffine_complZeroLocusOpen_of_cohomologicalDimension_eq_one A I hI hcd⟩

end Stacks.LocalCohomology

end
