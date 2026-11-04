module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.Homology.RelativelyPerfect.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# On an affine scheme the Tor clause of relative perfectness is Tor amplitude over the base

Let `R → A` be a ring map, let `f : Spec A ⟶ Spec R` be the associated morphism of affine schemes,
and let `E = M̃^•` be the derived sheafification of a complex `M^•` of `A`-modules. If the scalar
restriction of `E` to `f^{-1}𝒪_{Spec R}` locally has finite Tor dimension (the Tor clause of
Stacks 0DI0), then `E` has Tor amplitude in some interval `[a, b]` over `Spec R`, in the stalkwise
sense of Stacks 0C0V.

## Main results

* `exists_hasTorAmplitudeOver_of_locallyHasFiniteTorDimension`: the Tor clause of Stacks 0DI0
  yields stalkwise Tor amplitude over the base in one global interval.
* `exists_hasTorAmplitudeOver_of_isPerfectRelativeTo`: the same from `Spec R`-perfectness.

## Implementation notes

`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` of the scalar restriction of `M̃^•` to
`f^{-1}𝒪_{Spec R}`, at the canonical certificate family, is `HasFiniteTorDimensionCanonical R` of
`M^•` read over `R`, by
`AlgebraicGeometry.AffinePerfectDescent.locallyHasFiniteTorDimension_tildeObj_iff`, which is
Stacks 0DHY read at the canonical certificate; and that in turn is a global interval of stalkwise
Tor amplitude over the base, by
`AlgebraicGeometry.AffineRelativeTorAmplitude.exists_hasTorAmplitudeOver_tildeComplex_iff`. Both
are biconditionals.

Stacks 0DI0 is stated here at
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`, the derived tensor
product of Stacks 0BYI on each open subspace, which is the family Stacks 0DHY is compared at.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Lemma 36.19.3 (Tag 0C0V)](https://stacks.math.columbia.edu/tag/0C0V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **On an affine scheme the Tor clause of relative perfectness is stalkwise Tor amplitude over
the base, in one global interval.** The derived sheafification `M̃^•` of a complex of `A`-modules
whose scalar restriction to `f^{-1}𝒪_{Spec R}` locally has finite Tor dimension has Tor amplitude
in `[a, b]` over `f : Spec A ⟶ Spec R`, in the stalkwise sense of Stacks 0C0V, for some pair of
integers `a, b`. -/
theorem exists_hasTorAmplitudeOver_of_locallyHasFiniteTorDimension
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace (specMap R A).base)
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((Scheme.Hom.derivedScalarRestriction (specMap R A)).obj (tildeObj A M))) :
    ∃ a b : ℤ, HasTorAmplitudeOver (specMap R A) (tildeObj A M) a b :=
  (exists_hasTorAmplitudeOver_tildeComplex_iff R A M).2
    ((locallyHasFiniteTorDimension_tildeObj_iff R A M).1 h)

/-- **An `Spec R`-perfect sheafified complex on an affine scheme has finite Tor amplitude over the
base.** The derived sheafification `M̃^•` of a complex of `A`-modules which is `Spec R`-perfect at
the canonical certificate family has Tor amplitude in `[a, b]` over `f : Spec A ⟶ Spec R`, in the
stalkwise sense of Stacks 0C0V, for some pair of integers `a, b`. -/
theorem exists_hasTorAmplitudeOver_of_isPerfectRelativeTo [Module.Flat R A]
    [Algebra.FinitePresentation R A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : (specMap R A).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (tildeObj A M)) :
    ∃ a b : ℤ, HasTorAmplitudeOver (specMap R A) (tildeObj A M) a b :=
  exists_hasTorAmplitudeOver_of_locallyHasFiniteTorDimension R A M h.2

end AlgebraicGeometry.AffinePerfectDescent

end
