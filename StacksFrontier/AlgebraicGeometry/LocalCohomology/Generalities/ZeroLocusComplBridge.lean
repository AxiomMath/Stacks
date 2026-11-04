module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# The two constructions of the punctured spectrum agree

The open complement of the vanishing locus `V(I)` of an ideal in an affine spectrum is built
twice in this library: as `AlgebraicGeometry.zeroLocusCompl I` for an ideal of an object of
`CommRingCat`, and as `Stacks.LocalCohomology.complementZeroLocus R I` for an ideal of a bare
commutative ring. This file identifies them, so that a result stated in one vocabulary applies in
the other.

## Main results

* `AlgebraicGeometry.zeroLocusCompl_eq_complementZeroLocus`: the two opens are equal.
* `AlgebraicGeometry.zeroLocusCompl_toScheme_eq_complementZeroLocus`: so are the open subschemes
  they define, hence a module over either one is a module over the other.
* `AlgebraicGeometry.restrict_zeroLocusCompl_ι_eq`: so are the restrictions of a module on
  `Spec R` along the two open immersions.

## Implementation notes

Both opens are the complement of `PrimeSpectrum.zeroLocus (I : Set R)` and the carrier of
`CommRingCat.of R` is `R`, so every comparison below holds by `rfl`: nothing has to be
transported along the equality, and no isomorphism is needed in place of it. Instance synthesis
works at reducible transparency and therefore does not see these equalities, so a hypothesis such
as `F.IsCoherent` must be passed explicitly when moving between the two spellings.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The complement of `V(I)` in `Spec R` built from an ideal of `CommRingCat.of R` is the one
built from the same ideal of `R`. -/
theorem zeroLocusCompl_eq_complementZeroLocus :
    zeroLocusCompl (A := CommRingCat.of R) I = Stacks.LocalCohomology.complementZeroLocus R I :=
  rfl

/-- The open subschemes `Spec R ∖ V(I)` defined by the two constructions of that open are equal,
so a module over either one is a module over the other. -/
theorem zeroLocusCompl_toScheme_eq_complementZeroLocus :
    (zeroLocusCompl (A := CommRingCat.of R) I).toScheme =
      (Stacks.LocalCohomology.complementZeroLocus R I : Scheme) :=
  rfl

/-- Restricting a module on `Spec R` to `Spec R ∖ V(I)` along the open immersion of either
construction of that open gives the same module. -/
theorem restrict_zeroLocusCompl_ι_eq (G : (Spec (CommRingCat.of R)).Modules) :
    G.restrict (zeroLocusCompl (A := CommRingCat.of R) I).ι =
      G.restrict (Stacks.LocalCohomology.complementZeroLocus R I).ι :=
  rfl

end AlgebraicGeometry

end
