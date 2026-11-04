module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
import StacksCore.Tactic.StacksAttribute

/-! # Derived pullback against the comparison with the total tensor complex, with nothing left over

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `K` and `M` be
cochain complexes of `O_D`-modules. **Stacks 0FPH** asserts that the square whose two paths from
`Lf^*(K ⊗^L_{O_D} M)` to `Tot(f^*K ⊗_{O_C} f^*M)` are

* `Lf^*(K ⊗^L M) ⟶ Lf^*Tot(K ⊗ M) ⟶ f^*Tot(K ⊗ M) ⟶ Tot(f^*K ⊗ f^*M)` and
* `Lf^*(K ⊗^L M) ⟶ Lf^*K ⊗^L Lf^*M ⟶ f^*K ⊗^L f^*M ⟶ Tot(f^*K ⊗ f^*M)`

commutes.

`Stacks.Sheaves.DerivedPullback.derivedPullback_toTensor_square` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackTensorTotalSquare.lean`
proves exactly that, but in a binder context carrying seven instance arguments beyond the data of
the source: the existence of the left derived functor `Lf^*`, the additivity of `⊗_O` in each
variable on either side, and the existence of the total tensor complexes on either side.
**This file discharges all seven**, so Stacks 0FPH holds with no input beyond `f` being a morphism
of ringed topoi and `K`, `M` being complexes.

## How the instance arguments are discharged

The six tensor-side arguments are not hypotheses at all: `Stacks.SheafOfModules.Tensor`'s
`sheafTensor_additive`, `sheafTensor_obj_additive` and `hasMapBifunctor_sheafTensor` are global
instances, available from the sheafification hypotheses on the two sites alone, so instance
search supplies them once they are not shadowed by binders.

The seventh is the existence of `Lf^*`. It is a `Prop` class and cannot be a global instance
here, because it holds of a morphism of ringed topoi and `AlgebraicGeometry.RingedToposSiteHom`
is weaker than that: continuity of `f.u` is a field of it, left exactness of `f^{-1}` is not.
What supplies the missing exactness is `hmos`, and
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy` turns
`hmos` into the instance — this is the existence assertion of Stacks 06YY, which the proof of
Stacks 0FPH uses and which is unconditional in this tree. So the statement below supplies it
from `hmos` rather than asking for it, and by proof irrelevance `derivedPullback f` is the same
functor it was.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullback_toTensor_square_unconditional`:
  **Stacks 0FPH**, with the hypothesis shape of the source.

## Implementation notes

Nothing is restated: the square, every arrow in it and the whole of the argument are the
conditional theorem's, applied once with the discharged instance supplied. The instance is
supplied by `haveI` inside the statement rather than by a binder, which is what makes the
printed signature carry only `f`, `hmos` and the two complexes; the `haveI` reduces away, so the
statement is literally the equation of the conditional theorem.

What remains narrower than the source is not a hypothesis but the *presentation*: the morphism
of ringed topoi is one presented by a morphism of the underlying sites, over
`RingedTopos.{u, u, u}`. Passing from an arbitrary morphism of ringed topoi
(`AlgebraicGeometry.RingedToposHom`) to a site presentation is Stacks 03CI and is a library-wide
transport — every input of the proof (Stacks 07A4, 06YY, 0G7E, 03EL) exists only in the
site-presented form — so it is recorded in the tag note, as the `@[stacks 07A6]` note of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/OrdinaryAndDerivedCounit.lean`
records it for the derived adjunction.

## References

* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

include hmos in
/-- **Stacks 0FPH.** For a morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and cochain
complexes `K`, `M` of `O_D`-modules, the square formed by the canonical maps from the derived
tensor product to the ordinary total tensor complex, the comparison
`Lf^*(K ⊗^L_{O_D} M) ⟶ Lf^*K ⊗^L_{O_C} Lf^*M` of Stacks 07A4 followed by the derived-to-degreewise
pullback comparison in each tensor factor, and that same comparison followed by the
identification `f^*Tot(K ⊗_{O_D} M) ≅ Tot(f^*K ⊗_{O_C} f^*M)`, commutes.

The complexes are arbitrary and the only inputs are `f` and `hmos`. `hmos` is not a hypothesis
beyond the source's: it is this development's encoding of "`f` is a morphism of ringed topoi".
`AlgebraicGeometry.RingedToposSiteHom` presents the geometric morphism by a functor `f.u` between
the underlying sites and asks only that it be *continuous*; exactness of `f^{-1}` is not a field
of it, and along a merely continuous functor the inverse image need not be exact, so such an `f`
need not present a morphism of topoi at all. `CategoryTheory.Functor.IsMorphismOfSites` is
continuity together with that exactness — it is Stacks 00X1 — and it is exactly what
`AlgebraicGeometry.RingedToposSiteHom.toToposHom` consumes to produce the underlying morphism of
topoi.

The existence of `Lf^*` is not assumed: it is `hasLeftDerivedFunctor_pullbackOnHomotopy`, the
existence assertion of Stacks 06YY, which holds along every morphism of ringed topoi. -/
@[stacks 0FPH "for a morphism of ringed topoi presented by a morphism of the underlying sites,
at RingedTopos.{u, u, u}"]
theorem derivedPullback_toTensor_square_unconditional
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor K M) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos K M).hom =
      derivedPullbackTensorComparison f hmos (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj M) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f K) (pullbackComparisonQ f M) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj M) :=
  have := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  derivedPullback_toTensor_square f hmos K M

end Stacks.Sheaves.DerivedPullback

end
