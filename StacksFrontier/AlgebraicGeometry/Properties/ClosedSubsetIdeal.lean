module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute

/-!
# A finite ideal defining a closed subset on an affine open

Let `Z` be a closed subset of a scheme whose open complement is retrocompact. On every affine open,
`Z` is cut out by a finitely generated ideal of the ring of sections. Since `Scheme.zeroLocus` for
sections over `U` contains the complement of `U`, the equality is stated after intersecting both
sides with `U`.

## Main results

* `AlgebraicGeometry.exists_fg_ideal_zeroLocus_eq_inter`: a closed subset with retrocompact
  complement is defined on an affine open by a finitely generated ideal.

## References

* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- On an affine open of a scheme, a closed subset with retrocompact complement is the
zero locus of a finitely generated ideal of the ring of sections. -/
@[stacks 07ZP "finite_ideal_for_closed_subset_on_affine"]
lemma exists_fg_ideal_zeroLocus_eq_inter (X : Scheme.{u}) (Z : Set X)
    (hZ : IsClosed Z) (hZc : IsRetrocompact Zᶜ) (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ I : Ideal Γ(X, U), I.FG ∧
      Z ∩ (U : Set X) = X.zeroLocus (U := U) I ∩ (U : Set X) := by
  let f : PrimeSpectrum Γ(X, U) → X := hU.fromSpec.base
  have hopen : IsOpen (f ⁻¹' Zᶜ) :=
    hZ.isOpen_compl.preimage hU.fromSpec.isOpenEmbedding.continuous
  have hcpt : IsCompact (f ⁻¹' Zᶜ) :=
    (hZc.preimage_of_isOpenEmbedding hU.fromSpec.isOpenEmbedding).isCompact
  obtain ⟨I, hIFG, hI⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hcpt, hopen⟩
  refine ⟨I, hIFG, ?_⟩
  have hpre : f ⁻¹' Z = PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) := by
    rw [← compl_compl (PrimeSpectrum.zeroLocus (I : Set Γ(X, U))), hI,
      Set.preimage_compl, compl_compl]
  rw [← hU.fromSpec_image_zeroLocus I, ← hU.range_fromSpec,
    ← Set.image_preimage_eq_inter_range]
  exact congrArg (hU.fromSpec.base '' ·) hpre

end AlgebraicGeometry

end
