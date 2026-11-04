module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiAffine

/-!
# Upper semi-continuity of the derived-fibre Betti functions

Let `X` be a scheme and let `E` be a pseudo-coherent object of `D(𝒪_X)`.  For `i : ℤ` the `i`-th
derived-fibre Betti function of `E` sends a point `x` to `dim_{κ(x)} H^i(Li_x^* E)`.  This module
proves part (2) of [Stacks, Tag 0BDI]: that function is upper semi-continuous.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti`: **part (2) of
  [Stacks, Tag 0BDI].**

## Implementation notes

The assertion is local on `X`, and
`AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti_of_openImmersions`
is that reduction: it suffices that every point be in the image of an open immersion along which
the derived-fibre Betti function of the derived pullback is upper semi-continuous.  The open
immersions used are `AlgebraicGeometry.IsAffineOpen.fromSpec` for the affine opens of `X`, whose
sources are spectra of rings on the nose, so the affine case
`AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti_spec` applies
directly; pseudo-coherence of the derived pullback is
`AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_derivedPullback`, part of the base-change
half of the tag.

### Part (3) is proved elsewhere

Part (3) of the tag, that the level sets of the derived-fibre Betti functions are locally
constructible, is not proved in *this* file.  It is
`AlgebraicGeometry.DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage` of
`StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiConstructible`, under the same single
hypothesis as part (2): pseudo-coherence of `E`.

The reduction to the affine case there is the same one as here —
`AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens` ([Stacks, Tag 054C]) with
`AlgebraicGeometry.IsAffineOpen.fromSpec` a homeomorphism onto its open image and
`Topology.Homeomorph.isConstructible_preimage_iff`, the bridge
`AlgebraicGeometry.DerivedFibreBetti.exists_isPseudoCoherent_derivedFiberBetti_eq` carrying it
onto the level sets of `StacksDraft.Perfect.fibreBetti` on `PrimeSpectrum R`.  The affine case
cannot come from part (2): upper semi-continuity makes `{β_i ≤ n}` open and a level set a
difference of two such opens, but constructibility needs those opens *retrocompact*, which
semi-continuity does not give.  It is obtained instead, as in the source, from the rank loci of a
bounded-above finite free model `F`, where `β_i(p) = rank F^i - rank_p(d^{i-1}) - rank_p(d^i)` and
`{p | r ≤ rank_p(A)}` is the complement of the zero locus of the finitely generated ideal of
`r × r` minors of `A`, hence retrocompact by
`PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg`.  The rank dictionary that argument runs on
is `StacksDraft.MinorRank.minorIdeal_eq_top_iff_le_rank`
(`StacksFrontier/LinearAlgebra/Matrix/MinorIdealRank.lean`), with
`Stacks.DeterminantalRank.exteriorPower_map_ne_zero_iff_exists_minor`
(`StacksFrontier/LinearAlgebra/Matrix/DeterminantalRank.lean`).

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DerivedFibreBetti

/-- **[Stacks, Tag 0BDI], part (2): the derived-fibre Betti functions are upper
semi-continuous.**  Let `X` be a scheme and let `E` be a pseudo-coherent object of `D(𝒪_X)`.  For
every `i` the function `x ↦ dim_{κ(x)} H^i(Li_x^* E)` is upper semi-continuous on `X`.

Every point lies in an affine open `U`, and `U` is the image of the open immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X`; the derived pullback of `E` along it is pseudo-coherent, so the
affine case applies there, and upper semi-continuity is local on the source. -/
@[stacks 0BDI "part (2): for E a pseudo-coherent object of D(O_X) on a scheme X, the function \
beta_i sending x to dim_{kappa(x)} H^i(Li_x^* E) is upper semi-continuous. beta_i is \
AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti, the dimension over the residue field of \
the degree-i cohomology of the derived fibre read through global sections on Spec kappa(x), and \
pseudo-coherence of E is the only hypothesis"]
public theorem upperSemicontinuous_derivedFiberBetti (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) :
    UpperSemicontinuous (derivedFiberBetti X E hE i) := by
  refine upperSemicontinuous_derivedFiberBetti_of_openImmersions X E hE i fun x => ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  obtain ⟨y, hy⟩ : x ∈ Set.range U.2.fromSpec.base := by
    rw [U.2.range_fromSpec]; exact hxU
  exact ⟨Spec Γ(X, U.1), U.2.fromSpec, U.2.isOpenImmersion_fromSpec, y, hy,
    upperSemicontinuous_derivedFiberBetti_spec Γ(X, U.1) _ _ i⟩

end AlgebraicGeometry.DerivedFibreBetti

end
