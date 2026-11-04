module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMapShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness

/-!
# The étale base change map along a short exact sequence

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. This file proves that the abelian sheaves `F` on `X_étale` at
which the base change map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` is an isomorphism are closed under
extensions: if `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and the map is invertible at `F₁` and `F₃`,
it is invertible at `F₂`.

Nothing is assumed of the square beyond commutativity.

## Main results

* `Stacks.EtaleCohomology.isTriangulated_etaleAbelianDerivedDirectImage`: the unbounded derived
  direct image `Rf_*` on abelian sheaves of the small étale sites is a triangulated functor.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_shortExact`: the class of
  abelian sheaves at which the derived base change map is invertible is closed under extensions.

## Implementation notes

A short exact sequence gives the distinguished triangle `F₁[0] ⟶ F₂[0] ⟶ F₃[0] ⟶ F₁[0]⟦1⟧` of
`D(X_étale)` (`DerivedCategory.singleTriangle`). Both `Rf_* ⋙ g^{-1}` and `(g')^{-1} ⋙ Rf'_*` are
triangulated: the inverse images because they are induced by exact functors, the derived direct
images because they are right derived functors of a triangulated functor out of the homotopy
category of an abelian category with K-injective resolutions. The base change map is compatible
with the shift (`Stacks.EtaleCohomology.natTransCommShift_etaleAbelianDerivedBaseChange`), so the
objects at which it is invertible form a triangulated subcategory
(`Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated`), which contains the middle vertex
of a distinguished triangle as soon as it contains the two others.

## References

* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **The unbounded derived direct image `Rf_*` on abelian sheaves of the small étale sites is a
triangulated functor**, for its canonical commutation with the shift. It is a right derived
functor, along the quasi-isomorphisms, of degreewise direct image followed by localization, which
is triangulated, and abelian sheaves on the small étale site admit K-injective resolutions. -/
public instance isTriangulated_etaleAbelianDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleAbelianDerivedDirectImage.{u, v} f).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective
    (etaleAbelianPushforwardToDerivedCategory.{u, v} f)
    (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImageUnit.{u, v} f)

/-- The class of abelian sheaves at which the derived étale base change map is invertible is closed
under extensions (two out of three, middle term). -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_shortExact
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (h : g' ≫ f = f' ≫ g)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact)
    (h₁ : IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h S.X₁))
    (h₃ : IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h S.X₃)) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h S.X₂) := by
  have := Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated _ _
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h)
  have := Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h)
  exact ObjectProperty.ext_of_isTriangulatedClosed₂
    (fun E => IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app E))
    hS.singleTriangle hS.singleTriangle_distinguished h₁ h₃

end Stacks.EtaleCohomology

end
