module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
import StacksCore.Tactic.StacksAttribute

/-!
# Ringed topoi of simplicial components

A sheaf of commutative rings on the total site of a simplicial-site situation induces a ringed
topos on every component. The component inclusion gives a canonical morphism of ringed topoi,
whose underlying geometric morphism is the component morphism of Stacks 09WG.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.totalRingedTopos`: the total site with its given
  sheaf of commutative rings.
* `CategoryTheory.SimplicialSiteSituation.componentRingedTopos`: a component with the
  restriction of that sheaf along the component inclusion.
* `CategoryTheory.SimplicialSiteSituation.componentRingedToposHom`: the canonical morphism to
  the total ringed topos.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentRingedTopos_restrictionIso` identifies the
  inverse image of the total structure sheaf along the component morphism with its restriction
  along the component inclusion.
* `CategoryTheory.SimplicialSiteSituation.componentRingedTopos_restrictionIso_forget` pins that
  identification to the canonical comparison of Stacks 09WG on underlying sheaves of sets, so
  it cannot be twisted by an automorphism of restriction.
* `CategoryTheory.SimplicialSiteSituation.componentRingedToposHom_toToposHom` identifies the
  underlying geometric morphism.

## Implementation notes

The component structure sheaf is literal restriction along the component inclusion, which is
continuous. Inverse image along the component *morphism of topoi* is not that restriction on the
nose — it is the sheafified restriction `g⁻¹G = (u^p G)^#` — but the two are canonically
isomorphic because the component inclusion is also cocontinuous, by
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` (Stacks 00XR
(1)). `componentRingedTopos_restrictionIso` transports that set-level comparison to sheaves of
commutative rings with
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso` and then applies the
comparison of transported operations with restriction,
`Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`. Since the first factor is the given
comparison on underlying sheaves of sets and the second is the identity there, the composite is
pinned, which is what `componentRingedTopos_restrictionIso_forget` states.

The ringed-topos morphism uses that pinned isomorphism and the canonical adjunction
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` on sheaves of commutative rings; its
underlying morphism of topoi is definitionally the morphism of Stacks 09WG.

### Correspondence with the removed inverse-image machinery

This tag was stated against a `CategoryTheory.AlgebraicSheafImage` family and three members of
`MorphismOfTopoi` — `inverseImageRing`, `inverseImageRingForgetIso` and `ringAdjunction` — which
have since been removed from this development and replaced, declaration for declaration, by the
following. The replacement is the same mathematics: both constructions transport the commutative
ring operations of a sheaf along the finite-limit-preserving geometric inverse image and leave
the underlying sheaf of sets unchanged on the nose. The removed family did it through internal
ring objects of the topos, the present one through the ring structure on sections.
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/RingedProjection.lean` records the
same substitution for the two parts of Stacks 08P8 that the removal had made unstatable.

* `MorphismOfTopoi.inverseImageRing` is now
  `Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor`.
* `MorphismOfTopoi.pushforwardRing` is now
  `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor`.
* `MorphismOfTopoi.ringAdjunction` is now
  `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`.
* `MorphismOfTopoi.inverseImageRingForgetIso` is now
  `Stacks.Sheaves.ToposPushforward.inverseImageCommRingForgetIso`.
* `AlgebraicSheafImage.mapRingSheaf`, instantiated at restriction along a continuous functor of
  sites, is now `Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`.
* `AlgebraicSheafImage.mapCommRing` applied to a natural isomorphism of braided functors is now
  `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso`.
* `AlgebraicSheafImage.externalRingSheaf` composed with the forgetful functor is now
  `Stacks.Sheaves.ToposPullback.forgetPullbackCommRingSheafIso`.

The sheafification hypothesis that the removed construction needed on sheaves of commutative
rings is not needed here: the four `GrothendieckTopology.HasSheafCompose` hypotheses of
`AlgebraicGeometry.RingedToposHom` are all instances for the component and total topologies,
because those sites and the sheaf values live in one universe.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible] Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor

namespace CategoryTheory.SimplicialSiteSituation

/-- The total ringed topos of a simplicial-site situation with a sheaf of commutative rings on
its total site. -/
def totalRingedTopos (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) : RingedTopos.{u, u, u} where
  C := S.totalCategory
  J := S.totalTopology
  O := O

/-- The ringed topos of a simplicial component, with structure sheaf given by literal
restriction of the total sheaf of commutative rings along the component inclusion. -/
noncomputable def componentRingedTopos (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    RingedTopos.{u, u, u} where
  C := S.component n
  J := S.componentTopology n
  O := ((componentFunctor S n).sheafPushforwardContinuous CommRingCat.{u}
    (S.componentTopology n) S.totalTopology).obj O

/-- On sheaves of sets, inverse image along the component morphism of topoi is restriction along
the component inclusion. This is the canonical comparison of Stacks 09WG, available because the
component inclusion is both cocontinuous and continuous. -/
noncomputable def componentRingedTopos_setRestrictionIso (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (componentMorphism S n).inverseImage ≅
      (componentFunctor S n).sheafPushforwardContinuous (Type u)
        (S.componentTopology n) S.totalTopology :=
  (componentFunctor S n).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type u) (S.componentTopology n) S.totalTopology

/-- The inverse image of sheaves of commutative rings along the component morphism of topoi is
canonically and naturally isomorphic to restriction along the component inclusion. -/
@[stacks 0D72 "component_ringed_topos"]
noncomputable def componentRingedTopos_restrictionIso (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    inverseImageCommRingFunctor (J := S.componentTopology n) (K := S.totalTopology)
        (componentMorphism S n) ≅
      (componentFunctor S n).sheafPushforwardContinuous CommRingCat.{u}
        (S.componentTopology n) S.totalTopology :=
  (pullbackCommRingSheafFunctorIsoOfNatIso (S.componentTopology n)
        (componentRingedTopos_setRestrictionIso S n)).trans
    (restrictionCommRingNatIso (S.componentTopology n) S.totalTopology (componentFunctor S n))

/-- The restriction isomorphism is the canonical comparison of Stacks 09WG after forgetting the
ring operations. In particular its scalar map is not an arbitrary natural automorphism of
restriction. -/
@[stacks 0D72 "component_ringed_topos"]
theorem componentRingedTopos_restrictionIso_forget (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) (O : Sheaf S.totalTopology CommRingCat.{u}) :
    (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        ((componentRingedTopos_restrictionIso S n).hom.app O) =
      (inverseImageCommRingForgetIso (S.componentTopology n)
          (componentMorphism S n)).hom.app O ≫
        ((componentFunctor S n).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
          (Type u) (S.componentTopology n) S.totalTopology).hom.app
          ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) := by
  rw [componentRingedTopos_restrictionIso, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, pullbackCommRingSheafFunctorIsoOfNatIso_hom_app,
    pullbackCommRingSheafIsoOfNatIso_hom_forget, restrictionCommRingNatIso_hom_app,
    restrictionCommRingIso_hom_forget, inverseImageCommRingForgetIso_hom_app]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The canonical morphism of ringed topoi from a simplicial component to the total site. Its
structure map is the adjoint of the comparison `gₙ⁻¹O ⟶ Oₙ` of structure sheaves. -/
@[stacks 0D72 "component_ringed_topos"]
noncomputable def componentRingedToposHom (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    RingedToposHom (componentRingedTopos S O n) (totalRingedTopos S O) where
  toToposHom := componentMorphism S n
  fSharp := (commRingImageAdjunction (componentMorphism S n)).homEquiv O
    ((componentRingedTopos S O n).O)
    ((componentRingedTopos_restrictionIso S n).hom.app O)

/-- The underlying geometric morphism is the component morphism of Stacks 09WG. -/
@[stacks 0D72 "component_ringed_topos"]
theorem componentRingedToposHom_toToposHom (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    (componentRingedToposHom S O n).toToposHom = componentMorphism S n :=
  rfl

end CategoryTheory.SimplicialSiteSituation

end
