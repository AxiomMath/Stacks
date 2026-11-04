module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism

/-!
# The derived stalk of a derived pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `x : X` and `K` a K-flat complex
of `𝒪_Y`-modules. This file computes the stalk at `x` of `Lf^* K` in the derived category:

`(Lf^* K)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} K_{f x}`,

the right-hand side being the degreewise base change of the stalk complex of `K` at `f x`, and
records that that complex is K-flat over `𝒪_{Y,f x}` — so the degreewise tensor product *is* the
derived one, with no further resolution.

The file assembles three earlier results, listed in the implementation notes.

## Main results

* `Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`: on a K-flat complex `Lf^*` is degreewise
  pullback, read in the derived category at `DerivedCategory.Q`.
* `Stacks.Cohomology.derivedStalkDerivedPullbackIso`: the computation of the derived stalk.
* `Stacks.Cohomology.kFlatStalkwise_of_kFlatComplex`: the stalk complexes of a K-flat complex are
  K-flat over the stalk rings, which is what makes the right-hand side a derived tensor product.

## Implementation notes

The three inputs, in the order they are used:

* `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` (Stacks
  06YJ, "computation on K-flat complexes") makes
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f` invertible at a
  K-flat complex. Passing from the homotopy-category spelling it is stated in to
  `DerivedCategory.Q` is `DerivedCategory.quotientCompQhIso` at both ends and
  `Functor.mapHomotopyCategoryFactors` in the middle; none of that is content.
* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors` turns the derived stalk of a
  `DerivedCategory.Q`-image into the stalk complex.
* `Stacks.RingedSpace.stalkModulePullbackComplexIso` (Stacks 0098 at `ComplexShape.up ℤ`) is the
  computation itself.

K-flatness of the stalk complex is stated as
`AlgebraicGeometry.SheafOfModules.KFlatStalkwise Y.sheaf K`, the whole stalkwise predicate,
rather than `CochainComplex.KFlat` at the single point `f x`. That is not a choice of
convenience: `CochainComplex.KFlat` is stated for `ModuleCat R` with `R` commutative, so its
`ModuleCat` carries the `CommRing.toRing` spelling of the ring structure, while
`AlgebraicGeometry.SheafOfModules.stalkComplex` carries the `RingCat` one. The two are
definitionally equal, and the application at a named point does not elaborate: the `CommRing`
instance `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` is registered for
`Stacks.SheafOfModules.Tensor.ringSheaf R` and is not found at the `structureSheafRing Y`
spelling this file's complexes are written with. Stating the stalkwise predicate as a whole
leaves the instance resolution where it already works.

`Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K`,
`Stacks.SheafOfModules.IsKFlat Y.sheaf K` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K` are the same predicate (see the
implementation notes of `StacksFrontier/Topology/Sheaves/Cohomology/KFlatAndDerivedPullback/ResolvingDatumUnconditional.lean`), so the
hypothesis crosses between the two developments by a term-mode application and no transport.

The derived-stalk computation is one of the inputs of Stacks 0E23, the assertion that a base
change comparison is an isomorphism; it is itself Stacks 0098 transported to the derived category.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.Cohomology

universe w₁ w₂ u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)

/-- **A K-flat complex computes the derived pullback**, in the derived category rather than in
the homotopy category: `Lf^* K ≅ f^* K` for `K` K-flat, both sides read through
`DerivedCategory.Q`.

This is `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` with
the three localization comparisons applied at either end. The two models of the derived categories
are binders rather than the file's pinned `HasDerivedCategory.standard`: nothing in the argument
looks at the model. -/
def derivedPullbackIsoPullbackOfKFlat
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  haveI := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    f K hK
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).app K).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj K)) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _

/-- **The derived stalk of a derived pullback.** For a K-flat complex `K` of `𝒪_Y`-modules and a
point `x` of `X`, the stalk at `x` of `Lf^* K` in the derived category of `𝒪_{X,x}`-modules is
the degreewise base change along the germ map `𝒪_{Y,f x} ⟶ 𝒪_{X,x}` of the stalk complex of `K`
at `f x`:

`(Lf^* K)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} K_{f x}`.

By `kFlatStalkwise_of_kFlatComplex` the stalk complex `K_{f x}` is K-flat over `𝒪_{Y,f x}`, so
the degreewise tensor product on the right is the derived tensor product. -/
def derivedStalkDerivedPullbackIso (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K)
    (x : X.carrier) :
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        (((Stacks.RingedSpace.stalkBaseChange f x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
            (f.hom.base x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).mapIso
      (derivedPullbackIsoPullbackOfKFlat f K hK) ≪≫
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors (structureSheafRing X) x).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Stacks.RingedSpace.stalkModulePullbackComplexIso f x (ComplexShape.up ℤ)).app K)

/-- **The stalk complexes of a K-flat complex are K-flat.** Applied at `f x` this is what makes
the right-hand side of `derivedStalkDerivedPullbackIso` a derived tensor product rather than
merely a degreewise one.

This is `Stacks.SheafOfModules.KFlatPullback.stalkCriterion` — Stacks 06YB at a ringed space, with
no hypotheses left — read in the direction that goes from K-flatness to stalkwise K-flatness. -/
theorem kFlatStalkwise_of_kFlatComplex
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    AlgebraicGeometry.SheafOfModules.KFlatStalkwise Y.sheaf K :=
  Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlatStalkwise_of_kFlat Y K hK

end Stacks.Cohomology

end

end
