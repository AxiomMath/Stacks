module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex at a point of a site

Let `C` be a site, let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on `C`
and let `p` be a point of `C`. Then the stalk of the cotangent complex of `a` at `p` is the
cotangent complex of the induced homomorphism of stalks: `(L_{B/A})_p = L_{B_p/A_p}`.

This is the inverse image of the cotangent complex along a morphism of topoi
(`CategoryTheory.Sheaf.inverseImageCotangentComplexIso`) for the morphism of topoi
`CategoryTheory.Sheaf.pointToposMorphism`: the point `p` read as a morphism of topoi out of the
sheaves for the trivial topology on the one-point site `Stacks.Sheaves.RingedPoint.PointSite`,
through the identification `Sh(pt) = Sets` of `Stacks.Sheaves.RingedPoint.pointSiteSheafEquiv`.

## Main definitions

* `CategoryTheory.Sheaf.pointToposEquiv`: sheaves of sets for the trivial topology on the
  one-point site are sets.
* `CategoryTheory.Sheaf.pointToposMorphism`: a point of `C`, read as a morphism of topoi out
  of the topos of the one-point site.

## Main results

* `CategoryTheory.Sheaf.stalkCotangentComplexIso`: the stalk of the cotangent complex is the
  cotangent complex of the stalks.
* `CategoryTheory.Sheaf.pointToposMorphismInverseImageIso`: the inverse image along
  `pointToposMorphism` is the stalk functor `p⁻¹`.
* `CategoryTheory.Sheaf.pointInverseImageRingIso`: the sheaf of rings `f⁻¹B` on the one-point
  site is the stalk `B_p`.
* `CategoryTheory.Sheaf.pointStalkModuleSheafIso`: the underlying set of the inverse image of
  a sheaf of modules along the point is the stalk of its underlying sheaf of sets, naturally
  in the module.

## Implementation notes

The one-point site is taken in the universes of the objects and morphisms of `C`, so the
sections of the sheaves on it lie in the universe `max u v w` of the sections of `A` and `B`;
the point's universe of sets is `max u v w` as well.

## References

* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedPoint (PointSite pointSiteSheafEquiv)
open Stacks.Sheaves.RingedToposModules (inverseImageModules)
open Stacks.Sheaves.RingedToposModules (inverseImageModuleSheafIso)
open Stacks.Sheaves.ToposPushforward (inverseImageRingSheaf)

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (p : PointOfTopos.{max u v w, v, u} J)

/-- Sheaves of sets for the trivial topology on the one-point site are sets: the topos of the
point, in the universes of the site `C` and of the sections. -/
@[sga "4 IV 4.6.2" "partial", sga "7 VII 1.1.2.1" "partial"]
noncomputable def pointToposEquiv :
    Sheaf (⊥ : GrothendieckTopology (PointSite.{v, u})) (Type (max u v w)) ≌
      Type (max u v w) :=
  pointSiteSheafEquiv

/-- A point `p` of a site, read as a morphism of topoi out of the topos of the one-point site:
its inverse image is the stalk functor of `p` and its direct image is the skyscraper functor
of `p`, both composed with the identification `Sh(pt) = Sets`. -/
noncomputable def pointToposMorphism :
    MorphismOfTopoi (Sheaf (⊥ : GrothendieckTopology (PointSite.{v, u})) (Type (max u v w)))
      (Sheaf J (Type (max u v w))) where
  pushforward := (pointToposEquiv.{u, v, w}).functor ⋙ p.pushforward
  inverseImage := p.inverseImage ⋙ (pointToposEquiv.{u, v, w}).inverse
  adj := p.adj.comp (pointToposEquiv.{u, v, w}).symm.toAdjunction
  preservesFiniteLimits := by
    let _ : PreservesFiniteLimits (pointToposEquiv.{u, v, w}).inverse := inferInstance
    let _ : PreservesFiniteLimits p.inverseImage := p.preservesFiniteLimits
    exact comp_preservesFiniteLimits _ _

/-- The inverse image along `CategoryTheory.Sheaf.pointToposMorphism` is the stalk functor of
the point: taking the inverse image of a sheaf of sets and then reading the result as a set
through `Sh(pt) = Sets` is `p⁻¹`. -/
noncomputable def pointToposMorphismInverseImageIso :
    (pointToposMorphism.{u, v, w} J p).inverseImage ⋙ (pointToposEquiv.{u, v, w}).functor ≅
      p.inverseImage :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pointToposEquiv.{u, v, w}).counitIso ≪≫ Functor.rightUnitor _

/-- The underlying sheaf of sets of the inverse image of a sheaf of commutative rings along
the point is the stalk of its underlying sheaf of sets: the sheaf of rings `f⁻¹B` on the
one-point site is the stalk `B_p`. -/
noncomputable def pointInverseImageRingIso (B : Sheaf J CommRingCat.{max u v w}) :
    (pointToposEquiv.{u, v, w}).functor.obj
        ((sheafCompose (⊥ : GrothendieckTopology (PointSite.{v, u}))
          (forget CommRingCat.{max u v w})).obj
            ((pointToposMorphism.{u, v, w} J p).inverseImageRing.obj B)) ≅
      p.inverseImage.obj ((sheafCompose J (forget CommRingCat.{max u v w})).obj B) :=
  eqToIso (congrArg (pointToposEquiv.{u, v, w}).functor.obj
      ((pointToposMorphism.{u, v, w} J p).inverseImageRing_forget B)) ≪≫
    (pointToposMorphismInverseImageIso.{u, v, w} J p).app _

/-- The underlying set of the inverse image of a sheaf of modules along the point is the stalk
of its underlying sheaf of sets, naturally in the module. -/
noncomputable def pointStalkModuleSheafIso (B : Sheaf J CommRingCat.{max u v w}) :
    (inverseImageModules.{max u v w, max u v w, v, u, v, u}
            (pointToposMorphism.{u, v, w} J p)
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) B) ⋙
          moduleSheafFunctor.{max u v w, v, u}
            (inverseImageRingSheaf.{max u v w, max u v w, v, u, v, u}
              (pointToposMorphism.{u, v, w} J p)
              ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) B))) ⋙
        (pointToposEquiv.{u, v, w}).functor ≅
      moduleSheafFunctor.{max u v w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) B) ⋙
        p.inverseImage :=
  Functor.isoWhiskerRight
      (inverseImageModuleSheafIso.{max u v w, max u v w, v, u, v, u}
        (pointToposMorphism.{u, v, w} J p)
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) B))
      (pointToposEquiv.{u, v, w}).functor ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (moduleSheafFunctor.{max u v w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) B))
        (pointToposMorphismInverseImageIso.{u, v, w} J p)

variable {A B : Sheaf J CommRingCat.{max u v w}} (a : A ⟶ B)

/-- The stalk of the cotangent complex of a homomorphism of sheaves of commutative rings on a site
at a point of the site is the cotangent complex of the induced homomorphism of stalks:
`(L_{B/A})_p = L_{B_p/A_p}`. -/
@[stacks 08T0 "for a point whose universe of sets is the universe of the sections of the two
sheaves of rings, as in 08SV, and with the point read as a morphism of topoi out of the
sheaves for the trivial topology on the one-point site, taken in the universes of the objects
and the morphisms of the site. Both sides are cotangent complexes of a homomorphism of sheaves
of commutative rings, the right-hand one on the one-point site rather than of the homomorphism
of stalk rings itself: the identification of sheaves of modules on the one-point site with
modules over the stalk ring is not used. The identification of that topos with sets is
pointToposEquiv, of the inverse image along it with the stalk functor is
pointToposMorphismInverseImageIso, of the inverse image of the sheaves of rings with the stalk
rings is pointInverseImageRingIso, and of the terms of the left-hand side with the stalks of
the terms of the cotangent complex is pointStalkModuleSheafIso"]
noncomputable def stalkCotangentComplexIso :
    ((inverseImageTargetModules.{u, v, w, u, v, w}
            (⊥ : GrothendieckTopology (PointSite.{v, u})) J
            (pointToposMorphism.{u, v, w} J p)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v, w} J a) ≅
      cotangentComplex.{u, v, w} (⊥ : GrothendieckTopology (PointSite.{v, u}))
        ((pointToposMorphism.{u, v, w} J p).inverseImageRing.map a) :=
  inverseImageCotangentComplexIso.{u, v, w, u, v, w}
    (⊥ : GrothendieckTopology (PointSite.{v, u})) J (pointToposMorphism.{u, v, w} J p) a

end CategoryTheory.Sheaf

end
