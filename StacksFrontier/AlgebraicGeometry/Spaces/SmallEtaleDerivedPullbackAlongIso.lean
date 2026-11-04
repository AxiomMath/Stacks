module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect

/-!
# The derived pullback of modules along an isomorphism of algebraic spaces

Let `B` be a big fppf site, `S` a scheme contained in it, and let `X`, `Y` be algebraic spaces
over `S`.  The derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` along a morphism `f : X ⟶ Y` is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, Tag 06YY for the morphism of small
étale ringed topoi of Stacks 03G8.  This file draws out the consequences, for an *isomorphism*
`e : X ≅ Y`, of the composition law of Stacks 0D6D together with the unit law `L(𝟙 X)^* ≅ 𝟭`:
that `Le^*` is an equivalence of derived categories, and that it both preserves and reflects
the perfectness of Stacks 08G5.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackHomInvIso` and
  `smallEtaleDerivedModulePullbackInvHomIso`: for `e : X ≅ Y`, the two round trips
  `L(e.inv)^* ⋙ L(e.hom)^* ≅ 𝟭 D(𝒪_X)` and `L(e.hom)^* ⋙ L(e.inv)^* ≅ 𝟭 D(𝒪_Y)`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackEquivalence`: `Le^*` as an equivalence
  `D(𝒪_Y) ≌ D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback_hom_iff`: derived pullback
  along an isomorphism preserves and reflects perfectness.

## Implementation notes

The unit law `L(𝟙 X)^* ≅ 𝟭` is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIdIso`.
The two round-trip isomorphisms are assembled from the composition law and the unit law and need
not satisfy the triangle identities; `CategoryTheory.Equivalence.mk` adjointifies the unit, and
the resulting equivalence has `Le^*` as its functor and `L(e.inv)^*` as its inverse.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The derived pullback along an isomorphism, composed with the derived pullback along its
inverse**, is the identity functor of `D(𝒪_X)`: Stacks 0D6D for `e.hom ≫ e.inv = 𝟙 X`, followed
by the unit law `L(𝟙 X)^* ≅ 𝟭`. -/
def smallEtaleDerivedModulePullbackHomInvIso (e : X ≅ Y) :
    smallEtaleDerivedModulePullback B S hS e.inv ⋙ smallEtaleDerivedModulePullback B S hS e.hom ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  smallEtaleDerivedModulePullbackCompIso B S hS e.hom e.inv ≪≫
    smallEtaleDerivedModulePullbackCongr B S hS e.hom_inv_id ≪≫
      smallEtaleDerivedModulePullbackIdIso B S hS X

/-- **The derived pullback along the inverse of an isomorphism, composed with the derived
pullback along the isomorphism**, is the identity functor of `D(𝒪_Y)`: Stacks 0D6D for
`e.inv ≫ e.hom = 𝟙 Y`, followed by the unit law `L(𝟙 Y)^* ≅ 𝟭`. -/
def smallEtaleDerivedModulePullbackInvHomIso (e : X ≅ Y) :
    smallEtaleDerivedModulePullback B S hS e.hom ⋙ smallEtaleDerivedModulePullback B S hS e.inv ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :=
  smallEtaleDerivedModulePullbackCompIso B S hS e.inv e.hom ≪≫
    smallEtaleDerivedModulePullbackCongr B S hS e.inv_hom_id ≪≫
      smallEtaleDerivedModulePullbackIdIso B S hS Y

/-- **The derived pullback along an isomorphism of algebraic spaces is an equivalence of derived
categories** `D(𝒪_Y) ≌ D(𝒪_X)`, with the derived pullback along the inverse isomorphism as its
inverse. -/
def smallEtaleDerivedModulePullbackEquivalence (e : X ≅ Y) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ≌
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  CategoryTheory.Equivalence.mk (smallEtaleDerivedModulePullback B S hS e.hom)
    (smallEtaleDerivedModulePullback B S hS e.inv)
    (smallEtaleDerivedModulePullbackInvHomIso B S hS e).symm
    (smallEtaleDerivedModulePullbackHomInvIso B S hS e)

/-- The functor of `smallEtaleDerivedModulePullbackEquivalence B S hS e` is the derived pullback
along `e.hom`. -/
@[simp]
theorem smallEtaleDerivedModulePullbackEquivalence_functor (e : X ≅ Y) :
    (smallEtaleDerivedModulePullbackEquivalence B S hS e).functor =
      smallEtaleDerivedModulePullback B S hS e.hom :=
  rfl

/-- The inverse of `smallEtaleDerivedModulePullbackEquivalence B S hS e` is the derived pullback
along `e.inv`. -/
@[simp]
theorem smallEtaleDerivedModulePullbackEquivalence_inverse (e : X ≅ Y) :
    (smallEtaleDerivedModulePullbackEquivalence B S hS e).inverse =
      smallEtaleDerivedModulePullback B S hS e.inv :=
  rfl

/-- **An object of `D(𝒪_Y)` is perfect precisely when its derived pullback along an isomorphism
`e : X ≅ Y` is perfect**: derived pullback along an isomorphism preserves and reflects the
perfectness of Stacks 08G5. -/
theorem isPerfect_smallEtaleDerivedModulePullback_hom_iff (e : X ≅ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
        ((smallEtaleDerivedModulePullback B S hS e.hom).obj E) ↔
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E :=
  ⟨fun h => RingedSite.IsPerfect.of_iso _ (isPerfect_smallEtaleDerivedModulePullback e.inv _ h)
      ((smallEtaleDerivedModulePullbackInvHomIso B S hS e).app E),
    isPerfect_smallEtaleDerivedModulePullback e.hom E⟩

end AlgebraicGeometry.Space

end
