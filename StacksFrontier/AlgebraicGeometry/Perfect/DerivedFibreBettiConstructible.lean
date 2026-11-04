module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiAffine
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Constructible.Homeomorph
public import StacksFrontier.Homology.Perfect.BettiConstructible

/-!
# Local constructibility of the level sets of the derived-fibre Betti functions

Let `X` be a scheme and let `E` be a pseudo-coherent object of `D(𝒪_X)`.  For `i : ℤ` the `i`-th
derived-fibre Betti function of `E` sends a point `x` to `dim_{κ(x)} H^i(Li_x^* E)`.  This module
proves part (3) of [Stacks, Tag 0BDI]: the level sets of that function are locally constructible
in `X`.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.isConstructible_derivedFiberBetti_spec_preimage`: the
  affine case.  A level set of the derived-fibre Betti function of a pseudo-coherent object of
  `D(𝒪_{Spec R})` is constructible.
* `AlgebraicGeometry.DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage`:
  **part (3) of [Stacks, Tag 0BDI].**

## Implementation notes

The assertion is local on `X` in the strong sense supplied by [Stacks, Tag 054C]
(`AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens`): it suffices that the
restriction of the level set to every affine open be constructible.  For an affine open `U` the
morphism `AlgebraicGeometry.IsAffineOpen.fromSpec` is an open immersion of `Spec Γ(X, U)` onto
`U`, hence a homeomorphism onto the subspace `U`, so `Homeomorph.isConstructible_preimage_iff`
turns the restriction into the preimage along it; and part (1) of the tag,
`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback`, identifies that preimage
with a level set of the derived-fibre Betti function of the derived pullback, which is
pseudo-coherent by `AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_derivedPullback`.

The affine case is the bridge of `DerivedFibreBettiAffine` followed by the module-theoretic
statement: `AlgebraicGeometry.DerivedFibreBetti.exists_isPseudoCoherent_derivedFiberBetti_eq`
presents the function as `StacksDraft.Perfect.fibreBetti` of a pseudo-coherent object of `D(R)`,
whose level sets are constructible by
`StacksDraft.Perfect.isConstructible_fibreBetti_preimage`.  That, and not part (2), is what makes
the result constructible rather than merely a difference of opens: upper semi-continuity presents
a level set as a difference of two opens, but constructibility needs those opens retrocompact,
which is what the ideal of minors of the differentials of a finite free model supplies.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 054C](https://stacks.math.columbia.edu/tag/054C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open scoped Set.Notation

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DerivedFibreBetti

/-! ### The affine case -/

/-- **The affine case of part (3) of [Stacks, Tag 0BDI].**  A level set of the derived-fibre Betti
function of a pseudo-coherent object of `D(𝒪_{Spec R})` is a constructible subset of `Spec R`.

The function is `StacksDraft.Perfect.fibreBetti` of a pseudo-coherent object of `D(R)` by
`exists_isPseudoCoherent_derivedFiberBetti_eq`, and the level sets of that are constructible on
`PrimeSpectrum R` by `StacksDraft.Perfect.isConstructible_fibreBetti_preimage`; the points of
`Spec R` are the primes of `R` and the two topologies agree. -/
public theorem isConstructible_derivedFiberBetti_spec_preimage (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace) E) (i : ℤ) (n : ℕ) :
    IsConstructible (derivedFiberBetti (Spec R) E hE i ⁻¹' {n}) := by
  obtain ⟨M, hM, hbetti⟩ := exists_isPseudoCoherent_derivedFiberBetti_eq R E hE
  rw [hbetti i]
  exact StacksDraft.Perfect.isConstructible_fibreBetti_preimage.{u} M hM i n

/-! ### Part (3) -/

/-- **[Stacks, Tag 0BDI], part (3): the level sets of the derived-fibre Betti functions are
locally constructible.**  Let `X` be a scheme and let `E` be a pseudo-coherent object of
`D(𝒪_X)`.  For every `i` and every `n` the set of points `x` with
`dim_{κ(x)} H^i(Li_x^* E) = n` is locally constructible in `X`.

By [Stacks, Tag 054C] it is enough to check that the restriction to each affine open `U` is
constructible.  The open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` is a homeomorphism onto the
subspace `U`, so that restriction is constructible exactly when its preimage along `fromSpec` is;
and that preimage is a level set of the derived-fibre Betti function of the derived pullback of
`E`, by part (1) of the tag, to which the affine case applies. -/
@[stacks 0BDI "part (3): for E a pseudo-coherent object of D(O_X) on a scheme X, the level sets \
of the functions beta_i are locally constructible in X. beta_i is \
AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti, the dimension over the residue field of \
the degree-i cohomology of the derived fibre read through global sections on Spec kappa(x), the \
level set at n is the preimage of the singleton n, and pseudo-coherence of E is the only \
hypothesis. The affine case is proved, not assumed: it is \
StacksDraft.Perfect.isConstructible_fibreBetti_preimage, which runs the source's argument \
through the rank loci of a bounded-above finite free model -- over a field the ideal of r-by-r \
minors of a matrix is the unit ideal exactly when r is at most its rank \
(StacksDraft.MinorRank.minorIdeal_eq_top_iff_le_rank), so the locus where the rank at p is at \
least r is the complement of the zero locus of a finitely generated ideal and hence \
retrocompact, which is what semi-continuity does not give"]
public theorem isLocallyConstructible_derivedFiberBetti_preimage (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (i : ℤ) (n : ℕ) :
    IsLocallyConstructible (derivedFiberBetti X E hE i ⁻¹' {n}) := by
  refine (isLocallyConstructible_iff_forall_affineOpens _).2 fun U => ?_
  -- `Spec Γ(X, U)` is homeomorphic to the subspace `U` of `X`
  have hoi : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let e : ↥(Spec Γ(X, U.1)) ≃ₜ ↥((U.1 : Set X)) :=
    (Scheme.Hom.isOpenEmbedding (f := U.2.fromSpec)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr U.2.range_fromSpec)
  refine (e.isConstructible_preimage_iff _).1 ?_
  have hpre : e ⁻¹' ((U.1 : Set X) ↓∩ (derivedFiberBetti X E hE i ⁻¹' {n})) =
      derivedFiberBetti (Spec Γ(X, U.1))
        ((derivedPullback U.2.fromSpec.toLRSHom.toShHom).obj E)
        (isPseudoCoherent_derivedPullback U.2.fromSpec E hE) i ⁻¹' {n} := by
    rw [derivedFiberBetti_derivedPullback U.2.fromSpec E hE i]
    rfl
  rw [hpre]
  exact isConstructible_derivedFiberBetti_spec_preimage Γ(X, U.1) _ _ i n

end AlgebraicGeometry.DerivedFibreBetti

end
