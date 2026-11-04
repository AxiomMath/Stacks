module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedTildePushforward

/-!
# Derived affine sheafification with quasi-coherent codomain is an equivalence

Let `R` be a commutative ring. `AlgebraicGeometry.affineTildeQuasicoherent R` is derived
sheafification `M ↦ M̃` read as taking values in `D_QCoh(𝒪_{Spec R})`, and this file registers
the instance saying it is an equivalence, which is [Stacks, Tag 06Z0].

## Main results

* `AlgebraicGeometry.affineTildeQuasicoherent_isEquivalence` — derived affine sheafification
  `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence.

## Implementation notes

**Why this file exists.** `AlgebraicGeometry.affineTildeQuasicoherent` and
`AlgebraicGeometry.derivedTilde` are the *same* functor: both are
`CategoryTheory.ObjectProperty.lift` of `(tilde.functor R).mapDerivedCategory` along the property
that every cohomology sheaf is quasi-coherent, and their two quasi-coherence proofs —
`AlgebraicGeometry.affineTilde_isQuasicoherent` and
`AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj` — are proofs of the same
`Prop`, so the terms are definitionally equal. Instance search nevertheless does not find
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` for the first spelling, because
`affineTildeQuasicoherent` is a semireducible `def` and instance search unfolds only at reducible
transparency. The ascription below crosses the two spellings once, at default transparency, so
that no consumer has to.

**The model.** `AlgebraicGeometry.affineTildeQuasicoherent` is defined in a module that seats
`CategoryTheory.HasDerivedCategory.standard`, so its derived categories are not parameters of its
type: the standard model is baked into the term. The equivalence therefore has to come from
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` and not from
`AlgebraicGeometry.derivedTilde_isEquivalence` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`, which is at the locally
small model. For the same reason a file importing this one must write
`attribute [local instance 10000] HasDerivedCategory.standard`, not the plain attribute: the
import closure makes the locally small `HasDerivedCategory` declarations *global* instances, and a
global instance beats a default-priority local one.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **Stacks 06Z0.** Derived affine sheafification, read as taking values in the quasi-coherent
derived category, is an equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})`.

`AlgebraicGeometry.affineTildeQuasicoherent R` is definitionally
`AlgebraicGeometry.derivedTilde R`, so this is
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence`. -/
instance affineTildeQuasicoherent_isEquivalence (R : CommRingCat.{u}) :
    (affineTildeQuasicoherent R).IsEquivalence :=
  inferInstanceAs ((derivedTilde R).IsEquivalence)

end AlgebraicGeometry

end
