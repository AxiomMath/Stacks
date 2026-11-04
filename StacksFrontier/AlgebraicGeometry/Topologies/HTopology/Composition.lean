module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of morphisms of big h topoi

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a big h site, the morphism of big h
topoi attached to `f ≫ g` is canonically isomorphic to the composite of the morphisms
attached to `f` and to `g`, and the isomorphism is compatible with the geometric
adjunctions.

## Main definitions

* `AlgebraicGeometry.bigHMorphismOfTopoi_comp_pushforwardIso`: the comparison of direct
  images.
* `AlgebraicGeometry.bigHMorphismOfTopoi_comp_inverseImageIso`: the comparison of inverse
  images.

## Main results

* `AlgebraicGeometry.bigHMorphismOfTopoi_comp_unit`: the two comparisons are compatible with
  the units of the geometric adjunctions.

## Implementation notes

Composition of base-change functors on slices is canonical only up to natural isomorphism,
because an iterated fibre product and a single fibre product are canonically isomorphic
rather than equal.  The direct-image comparison is therefore induced by
`CategoryTheory.Over.pullbackComp` through the composition isomorphism for restriction along
continuous site functors, and the inverse-image comparison is its adjunction mate,
`CategoryTheory.Adjunction.leftAdjointCompIso`.  Being mates is exactly compatibility with
the units, which is what makes the pair an isomorphism of geometric morphisms.

## References

* [Stacks Project, Tag 0EU7](https://stacks.math.columbia.edu/tag/0EU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks 0EU7.** The direct image of the morphism of big h topoi attached to a composite
is canonically isomorphic to the composite of the direct images. -/
@[stacks 0EU7 "direct image"]
public noncomputable def bigHMorphismOfTopoi_comp_pushforwardIso (B : BigHSite.{u})
    {X Y Z : B.Schemes} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).pushforward ≅
      (bigHMorphismOfTopoi B (f ≫ g)).pushforward :=
  Functor.sheafPushforwardContinuousComp'
    (Over.pullbackComp f g).symm (Type (u + 1))
    (BigHOver.topology B Z.obj Z.property)
    (BigHOver.topology B Y.obj Y.property)
    (BigHOver.topology B X.obj X.property)

/-- **Stacks 0EU7.** The inverse image of the morphism of big h topoi attached to a composite
is canonically isomorphic to the composite of the inverse images; the isomorphism is the
adjunction mate of the comparison of direct images. -/
@[stacks 0EU7 "inverse image"]
public noncomputable def bigHMorphismOfTopoi_comp_inverseImageIso (B : BigHSite.{u})
    {X Y Z : B.Schemes} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).inverseImage ≅
      (bigHMorphismOfTopoi B (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso (bigHMorphismOfTopoi B g).adj
    (bigHMorphismOfTopoi B f).adj (bigHMorphismOfTopoi B (f ≫ g)).adj
    (bigHMorphismOfTopoi_comp_pushforwardIso B f g)

/-- **Stacks 0EU7.** The comparisons of direct and inverse images for a composite respect the
units of the geometric adjunctions, so together they form an isomorphism of morphisms of
topoi. -/
@[stacks 0EU7 "compatibility with the adjunction"]
public theorem bigHMorphismOfTopoi_comp_unit (B : BigHSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : Sheaf (BigHOver.topology B Z.obj Z.property) (Type (u + 1))) :
    (bigHMorphismOfTopoi B (f ≫ g)).adj.unit.app V ≫
        (bigHMorphismOfTopoi B (f ≫ g)).pushforward.map
          ((bigHMorphismOfTopoi_comp_inverseImageIso B f g).inv.app V) ≫
        (bigHMorphismOfTopoi_comp_pushforwardIso B f g).inv.app
          (((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).inverseImage.obj V) =
      ((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).adj.unit.app V := by
  have hinv : (bigHMorphismOfTopoi_comp_inverseImageIso B f g).inv.app V =
      (((conjugateEquiv ((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).adj
        (bigHMorphismOfTopoi B (f ≫ g)).adj).symm
          (bigHMorphismOfTopoi_comp_pushforwardIso B f g).hom).app V) := rfl
  have hunit := (unit_conjugateEquiv_symm
    ((bigHMorphismOfTopoi B g).comp (bigHMorphismOfTopoi B f)).adj
    (bigHMorphismOfTopoi B (f ≫ g)).adj
    (bigHMorphismOfTopoi_comp_pushforwardIso B f g).hom V).symm
  rw [hinv, ← Category.assoc, hunit, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

end AlgebraicGeometry
