module

public import StacksFrontier.AlgebraicGeometry.Modules.AffineOpenAssociatedSheafPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism

/-!
# The associated-sheaf complex on an affine open is a derived pullback

Let `V` be an affine open of a scheme `X`. Applying the construction of Stacks 01BH degreewise to
a complex of `Γ(X, V)`-modules and passing to `D(𝒪_V)` gives the derived pullback along
`V ≅ Spec Γ(X, V)` of the corresponding complex on `Spec Γ(X, V)`.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.associatedSheafComplexIsoDerivedPullback`.

## Implementation notes

The degreewise comparison is `AlgebraicGeometry.IsAffineOpen.associatedSheafPullbackIso` applied
to complexes through `CategoryTheory.Functor.mapHomologicalComplexCompIso`. Replacing the
resulting degreewise pullback by the derived pullback is
`CategoryTheory.Functor.mapDerivedCategoryFactors` followed by
`Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso`, which is
available because the affine comparison is an isomorphism; no K-flatness hypothesis on the
complex is needed.

The affine side is written as tensor sheafification along `Γ(X, V) → Γ(Spec Γ(X, V), 𝒪)` rather
than as `AlgebraicGeometry.tilde.functor`, whose codomain `AlgebraicGeometry.Scheme.Modules`
carries a `CategoryTheory.Preadditive` instance that instance search does not identify with the
one on `CategoryTheory.SheafOfModules`; the two are identified by
`AlgebraicGeometry.tilde.associatedSheafNatIso`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BJ](https://stacks.math.columbia.edu/tag/01BJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf (associatedSheafFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry.IsAffineOpen

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

/-- **The complex of associated sheaves on an affine open is the derived pullback along
`V ≅ Spec Γ(X, V)` of the complex of associated sheaves on `Spec Γ(X, V)`.** -/
def associatedSheafComplexIsoDerivedPullback :
    (associatedSheafFunctor.{u, u} V.toScheme.toRingedSpace
          V.topIso.inv.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      (associatedSheafFunctor.{u, u} (Spec Γ(X, V)).toRingedSpace
          (Scheme.ΓSpecIso Γ(X, V)).inv.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ derivedPullback hV.isoSpecRingedSpaceHom := by
  refine Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
      hV.associatedSheafPullbackIso (ComplexShape.up ℤ)).symm DerivedCategory.Q ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine Functor.isoWhiskerLeft _
    ((modulePullback hV.isoSpecRingedSpaceHom).mapDerivedCategoryFactors).symm ≪≫ ?_
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft DerivedCategory.Q
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso
      hV.isoSpecRingedSpaceHom).symm)

end AlgebraicGeometry.IsAffineOpen

end
