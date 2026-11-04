module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroDerivedBaseChange

/-!
# The base change isomorphism for derived extension by zero

Let

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  W
```

be a cartesian square of algebraic spaces with `u` and `u'` étale. The base change map
`u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` of
`AlgebraicGeometry.Space.DerivedPullbackComposition.extensionByZeroBaseChange` for the canonical
pseudofunctoriality datum of derived pullback is invertible at every object of `D(𝒪_U)`
(`AlgebraicGeometry.Space.isIso_extensionByZeroBaseChange_canonical_app_of_isPullback`), hence is
an isomorphism of functors `Lt'^* ⋙ u'_! ≅ u_! ⋙ Lt^*`.

## Main definitions

* `AlgebraicGeometry.Space.extensionByZeroBaseChangeIso`: the isomorphism
  `Lt'^* ⋙ u'_! ≅ u_! ⋙ Lt^*` of a cartesian square with `u`, `u'` étale.

## Main results

* `AlgebraicGeometry.Space.extensionByZeroBaseChangeIso_hom`: its forward direction is the base
  change map.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change isomorphism for derived extension by zero**: for a cartesian square

```
T' --u'--> T
|t'        |t
v          v
U  --u-->  W
```

of algebraic spaces with `u` and `u'` étale, the base change map
`u'_!(Lt'^*A) ⟶ Lt^*(u_!A)` of the canonical pseudofunctoriality datum of derived pullback is an
isomorphism of functors `Lt'^* ⋙ u'_! ≅ u_! ⋙ Lt^*`. -/
def extensionByZeroBaseChangeIso {T T' U W : AlgebraicSpaces B S hS} (u' : T' ⟶ T) (t : T ⟶ W)
    (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u) (hu : IsEtale B S hS u.hom)
    (hu' : IsEtale B S hS u'.hom) :
    smallEtaleDerivedModulePullback B S hS t' ⋙
        (etaleExtensionByZero B S hS u' hu').mapDerivedCategory ≅
      (etaleExtensionByZero B S hS u hu).mapDerivedCategory ⋙
        smallEtaleDerivedModulePullback B S hS t :=
  haveI : ∀ A, IsIso (((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange
      u' t t' u hu hu' sq.w).app A) :=
    isIso_extensionByZeroBaseChange_canonical_app_of_isPullback u' t t' u sq hu hu'
  haveI := NatIso.isIso_of_isIso_app
    ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu' sq.w)
  asIso ((DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu'
    sq.w)

/-- The forward direction of `AlgebraicGeometry.Space.extensionByZeroBaseChangeIso` is the base
change map for extension by zero. -/
theorem extensionByZeroBaseChangeIso_hom {T T' U W : AlgebraicSpaces B S hS} (u' : T' ⟶ T)
    (t : T ⟶ W) (t' : T' ⟶ U) (u : U ⟶ W) (sq : IsPullback u' t' t u)
    (hu : IsEtale B S hS u.hom) (hu' : IsEtale B S hS u'.hom) :
    (extensionByZeroBaseChangeIso u' t t' u sq hu hu').hom =
      (DerivedPullbackComposition.canonical B S hS).extensionByZeroBaseChange u' t t' u hu hu'
        sq.w :=
  rfl

end AlgebraicGeometry.Space

end
