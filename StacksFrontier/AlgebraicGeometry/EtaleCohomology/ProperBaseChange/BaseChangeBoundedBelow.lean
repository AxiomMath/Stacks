module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The étale base change map on bounded below complexes with torsion cohomology

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes, and suppose that cohomology commutes with base change for `f`:
the base change map `g^{-1}Rf_*F ⟶ Rf'_*(g')^{-1}F` is an isomorphism for every torsion abelian
sheaf `F` on `X_étale` and every such square. This file shows that the base change map
`g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` is then an isomorphism for every bounded below object `E` of the
derived category of abelian sheaves on `X_étale` whose cohomology sheaves are torsion.

This is the passage from sheaves to complexes in the proof of Stacks 0DDE: once the proper base
change theorem (Stacks 095T) supplies the hypothesis for a proper morphism `f`, the statement of
0DDE follows at once.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange`:
  the base change map is invertible on bounded below complexes with torsion cohomology sheaves.

## Implementation notes

The source argues with the spectral sequences `R^pf_*H^q(E) ⇒ R^{p+q}f_*E`. The argument here is
the equivalent dévissage along the truncation triangles of the canonical t-structure: the two
functors `Rf_* ⋙ g^{-1}` and `(g')^{-1} ⋙ Rf'_*` are triangulated and carry `D^{≥m}` into
`D^{≥m}` (inverse images are exact, `CategoryTheory.Functor.isGE_obj_mapDerivedCategory`, and the
unbounded right derived functor `Rf_*` is left t-exact,
`Stacks.DerivedFunctor.isGE_totalRightDerived_obj`), and
the base change map is compatible with the shift, so the generic statement
`CategoryTheory.NatTrans.isIso_app_of_isGE` reduces invertibility at a bounded below `E` to
invertibility at its cohomology sheaves placed in degree zero, which is the hypothesis.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **The base change map on bounded below complexes with torsion cohomology.** Suppose that
cohomology commutes with base change for `f : X ⟶ Y`, and let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square. For every object `E` of the derived category of abelian sheaves on
`X_étale` which is bounded below and has torsion cohomology sheaves, the base change map
`g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` is an isomorphism. -/
public theorem isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (n : ℤ)
    (hE : E.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology E) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w).app E) :=
  NatTrans.isIso_app_of_isGE (etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w)
    (fun L m hL ↦ by
      have := hL
      exact Functor.isGE_obj_mapDerivedCategory (etaleAbelianInverseImage.{u, v} g) _ m
        (Stacks.DerivedFunctor.isGE_totalRightDerived_obj (etaleAbelianDirectImage.{u, v} f) L m))
    (fun L m hL ↦ by
      have := Functor.isGE_obj_mapDerivedCategory (etaleAbelianInverseImage.{u, v} g') L m hL
      exact Stacks.DerivedFunctor.isGE_totalRightDerived_obj (etaleAbelianDirectImage.{u, v} f')
        _ m)
    E n hE (fun q ↦ hf g g' f' sq _ (hT q))

end Stacks.EtaleCohomology

end
