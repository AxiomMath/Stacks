module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of modules to a component is the literal restriction

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
Restriction of sheaves of `O`-modules to the degree-`n` component occurs in this development in
two never-identified presentations: the pullback of sheaves of modules along the component
morphism of ringed topoi `g_n` of Stacks 0D72, and the literal restriction of sections along the
component inclusion. This file identifies them.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentRingedToposHom_fSharpInverseImageRing`
  `_ringSheafMap`: the inverse-image form of the structure map of `g_n`, read at the level of
  sheaves of *rings* and then on underlying sheaves of sets, is the comparison of Stacks 09WG.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso`: **Stacks
  0D72**, `g_n^* ≅ (-)|_{C_n}`. The pullback of sheaves of modules along the component morphism
  of ringed topoi is the literal restriction of modules to the component.

## Implementation notes

The structure sheaf of the component ringed topos is by construction the literal restriction of
`O`, so the structure map of `g_n` is invertible
(`CategoryTheory.SimplicialSiteSituation.isIso_componentRingedToposHom_fSharpInverseImage`) and
the pullback of modules performs no genuine extension of scalars: by
`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`
it is the inverse image of modules followed by restriction of scalars along the inverse of the
structure map. The inverse image of modules is in turn the transport of modules along the
set-level comparison of Stacks 09WG
(`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`), and that transport is the
literal restriction (`CategoryTheory.SimplicialSiteSituation`
`.componentModulePullbackRestrictionIso`). Three restrictions of scalars are left, and their
composite map of sheaves of rings is the identity, so they cancel in one step by
`Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId'`.

*The choice of the scalar map.* `pullbackModuleFunctorIsoOfNatIso` takes the comparison `β` of
the two transported sheaves of rings as a parameter, subject to its underlying morphism of
sheaves of sets being the given comparison of transporting functors. Taking `β` to be the
inverse-image form of the structure map followed by the inverse of the restriction comparison of
Stacks 09WG makes the three-fold cancellation an `Iso.inv_hom_id` and nothing further: no
separate identification of `β` with anything is then owed.

*Why the hypothesis on `β` is proved through sheaves of commutative rings.* The structure map is
recorded in two forms, the commutative one in which Stacks 09WG is available and the ring one
along which scalars are extended;
`AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage` bridges them. It
cannot be rewritten *with* inside the goal: the ringed topos spells its site
`(S.componentRingedTopos O n).J` and Stacks 09WG spells it `S.componentTopology n`, and although
the two are equal by `Eq.refl` a rewrite across them cannot place its motive. So the comparison
is assembled from `Eq.trans` and `congrArg`, exactly as in
`CategoryTheory.SimplicialSiteSituation.forgetFSharp_componentRingedToposHom`.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- The comparison of Stacks 09WG between the inverse image of the total sheaf of rings along
the component morphism of topoi and its restriction along the component inclusion, read on
sheaves of rings. -/
abbrev componentRestrictionRingIso :=
  restrictionRingIso (S.componentTopology n) S.totalTopology (componentFunctor S n)
    (S.totalRingSheaf O)

/-- **The scalar map of the comparison of the two presentations of restriction to a component.**
The inverse-image form of the structure map of `g_n`, at the level of sheaves of rings, followed
by the inverse of the comparison of Stacks 09WG. This is the morphism along which the inverse
image of modules of Stacks 03D2 is read over the transported sheaf of rings. -/
def componentPullbackRestrictionRingMap :=
  (componentRingedToposHom S O n).fSharpInverseImageRing ≫
    (componentRestrictionRingIso S O n).inv

/-- The inverse of the structure map of `g_n`, at the level of sheaves of rings: the morphism
along which the pullback of modules restricts scalars back to the component structure sheaf. -/
def componentPullbackStructureInv :=
  (asIso (componentRingedToposHom S O n).toModulesHom.fSharpInverseImage).inv

/-- **The inverse-image form of the structure map of `g_n` on underlying sheaves of sets is the
comparison of Stacks 09WG.** The structure map is recorded through the adjunction for sheaves of
commutative rings and used through the adjunction for sheaves of rings; the two agree on
underlying sheaves of sets, where the first is Stacks 09WG by construction of the component
ringed topos. -/
@[stacks 0D72 "the structure map of the component morphism on underlying sheaves of sets"]
theorem componentRingedToposHom_fSharpInverseImageRing_ringSheafMap :
    (sheafCompose (S.componentTopology n) (forget RingCat.{u})).map
        (componentRingedToposHom S O n).fSharpInverseImageRing =
      (componentRingedTopos_setRestrictionIso S n).hom.app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) := by
  have hforget : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        ((componentRingedTopos_restrictionIso S n).hom.app O) =
      (S.componentRingedTopos_setRestrictionIso n).hom.app
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O) :=
    (componentRingedTopos_restrictionIso_forget S n O).trans
      ((congrArg (fun q ↦ q ≫ (S.componentRingedTopos_setRestrictionIso n).hom.app
            ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
          (inverseImageCommRingForgetIso_hom_app (S.componentTopology n)
            (componentMorphism S n) O)).trans (Category.id_comp _))
  rw [← AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
    (componentRingedToposHom S O n)]
  exact (congrArg (fun q ↦ (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map q)
    (componentRingedToposHom_fSharpInverseImage S O n)).trans hforget

/-- **The scalar map has the comparison of Stacks 09WG underneath.** This is the hypothesis of
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` at the comparison of
transporting functors of Stacks 09WG; the second factor of the scalar map is the identity on
underlying sheaves of sets. -/
theorem componentPullbackRestrictionRingMap_ringSheafMap :
    (sheafCompose (S.componentTopology n) (forget RingCat.{u})).map
        (componentPullbackRestrictionRingMap S O n) =
      (componentRingedTopos_setRestrictionIso S n).hom.app
        (Sheaf.ringSheaf.{u, u, u} (S.totalRingSheaf O)) :=
  ((sheafCompose (S.componentTopology n) (forget RingCat.{u})).map_comp _ _).trans
    ((congrArg
        (fun q ↦ (sheafCompose (S.componentTopology n) (forget RingCat.{u})).map
            (componentRingedToposHom S O n).fSharpInverseImageRing ≫ q)
        (restrictionRingIso_inv_ringSheafMap (S.componentTopology n) S.totalTopology
          (componentFunctor S n) (S.totalRingSheaf O))).trans
      ((Category.comp_id _).trans
        (componentRingedToposHom_fSharpInverseImageRing_ringSheafMap S O n)))

/-- **The three scalar maps compose to the identity.** The inverse of the structure map, the
structure map, and the two directions of the comparison of Stacks 09WG: everything cancels. -/
theorem componentPullbackStructureInv_comp :
    componentPullbackStructureInv S O n ≫
        (componentPullbackRestrictionRingMap S O n ≫ (componentRestrictionRingIso S O n).hom) =
      𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q ↦ q ≫ (componentRestrictionRingIso S O n).hom)
        (Iso.inv_hom_id_assoc (asIso (componentRingedToposHom S O n).fSharpInverseImageRing)
          (componentRestrictionRingIso S O n).inv)).trans
      (componentRestrictionRingIso S O n).inv_hom_id)

/-- The inverse image of sheaves of modules along the component morphism of topoi is the
transport along the comparison of Stacks 09WG of the inverse image along the set-level
restriction functor, the scalars being read along
`CategoryTheory.SimplicialSiteSituation.componentPullbackRestrictionRingMap`. -/
def componentInverseImageModulesRestrictionIso :=
  pullbackModuleFunctorIsoOfNatIso.{u, u, u, u, u, u} (S.componentTopology n)
    (S.totalRingSheaf O) (componentRingedTopos_setRestrictionIso S n)
    (componentPullbackRestrictionRingMap S O n)
    (componentPullbackRestrictionRingMap_ringSheafMap S O n)

/-- **Stacks 0D72: the pullback of sheaves of modules to a simplicial component is the literal
restriction.** The two presentations of restriction to the degree-`n` component that this
development carries — pullback of modules along the component morphism of ringed topoi, and
restriction of sections along the component inclusion — are canonically isomorphic. -/
@[stacks 0D72 "the pullback of modules along g_n is restriction to the component"]
def componentPullbackModulesRestrictionIso :
    (componentRingedToposHom S O n).toModulesHom.pullbackModules ≅
      S.componentModulesRestriction O n := by
  refine Iso.trans (Functor.isoWhiskerLeft _
    (componentRingedToposHom S O
      n).toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso) ?_
  refine Iso.trans
    (Functor.isoWhiskerRight (componentInverseImageModulesRestrictionIso S O n) _) ?_
  refine Iso.trans (Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (componentModulePullbackRestrictionIso S (S.totalRingSheaf O) n) _) _) ?_
  refine Iso.trans (Functor.associator _ _ _) ?_
  exact Functor.isoWhiskerLeft _ (Stacks.Sheaves.RingedPoint.sheafRestrictScalarsComp₃IsoId'
    (componentRestrictionRingIso S O n).hom (componentPullbackRestrictionRingMap S O n)
    (componentPullbackStructureInv S O n) (componentPullbackStructureInv_comp S O n))

end CategoryTheory.SimplicialSiteSituation

end
