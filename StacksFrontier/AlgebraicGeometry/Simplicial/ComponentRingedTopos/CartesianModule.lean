module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModulesMap
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cartesian sheaves of modules on the total site of a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site. A
sheaf of `O`-modules `F` restricts to a sheaf of `O_n`-modules `F_n = g_n^*F` on every component
ringed topos of Stacks 0D72, and a simplex map `φ : [m] ⟶ [n]` induces a canonical transition
`f_φ^*F_m ⟶ F_n`. The sheaf of modules is *cartesian* when every one of those transitions is an
isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition`: the comparison
  `g_m⁻¹ ⋙ f_φ⁻¹ ⟶ g_n⁻¹` of inverse images of sheaves of sets, the transition of Stacks 09WF
  read through the identification of inverse image along a component morphism of topoi with
  restriction.
* `CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism`: the resulting 2-morphism
  `g_n ⟶ g_m ∘ f_φ` of morphisms of ringed topoi, in the sense of Stacks 04IC.
* `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition`: the transition
  `f_φ^*F_m ⟶ F_n` of sheaves of modules.
* `CategoryTheory.SimplicialSiteSituation.IsModuleFiberTransitionIso`: the condition that
  every transition `moduleFiberTransition` of a sheaf of modules is an isomorphism, which is the
  cartesian condition of Stacks 07TF read through the 2-morphism of this file.

## Main results

* `CategoryTheory.SimplicialSiteSituation.forgetFSharp_componentRingedToposHom`: the structure
  map of the component morphism of ringed topoi is, on underlying sheaves of sets, the adjunct
  of the comparison of Stacks 09WG between inverse image and restriction.
* `CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism_commutes`: the 2-morphism
  is compatible with the structure maps, which is what makes it a 2-morphism of *ringed* topoi.

## Implementation notes

Restriction to the degree-`n` component is taken to be the pullback of sheaves of modules along
the component morphism of ringed topoi `g_n` of Stacks 0D72. The transition is then obtained in
one step from the 2-morphism `g_n ⟶ g_m ∘ f_φ`: a 2-morphism of ringed topoi induces a
transformation of the pullbacks of sheaves of modules the other way
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap`), and the pullback along the
composite splits by the pseudofunctoriality of Stacks 03D8.

The 2-morphism itself is the mate of the transition of Stacks 09WF. Its compatibility with the
structure maps is the only computation in this file, and it is a computation with adjuncts: by
`Stacks.CategoryTheory.homEquiv_conjugate` the left-hand side is the adjunct, along the
composite adjunction, of the inverse-image transition composed with the comparison of
Stacks 09WG; `CategoryTheory.Adjunction.comp_homEquiv` splits that adjunct into two, the inner
one is the direct-image transition by
`CategoryTheory.SimplicialSiteSituation.fiberTransition_adj`, and the outer one is the structure
map of `g_m` followed by the direct image of that transition. That is the structure map of the
composite, by `AlgebraicGeometry.RingedToposHom.forgetFSharp_comp` and
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom_forgetFSharp`.

Sheaves of modules are formed at the site universe, as in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`: the
sheafification of abelian sheaves that the pullback of modules is built from is available there
because the categories are small. The two instances are supplied locally, as in that file.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp
  MorphismOfTopoi.comp CategoryTheory.SimplicialSiteSituation.restrict
  CategoryTheory.SimplicialSiteSituation.componentRingedTopos

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- **Stacks 09WF, through the component morphisms of topoi.** The comparison
`g_m⁻¹ ⋙ f_φ⁻¹ ⟶ g_n⁻¹` of inverse images of sheaves of sets attached to a simplex map
`φ : [m] ⟶ [n]`: the inverse-image transition
`CategoryTheory.SimplicialSiteSituation.fiberTransition`, conjugated by the comparison of
Stacks 09WG between inverse image along a component morphism of topoi and restriction along the
component inclusion. -/
@[sga "4 VI 7.1.6" "special case"]
def componentInverseImageTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    ((componentMorphism S m).comp (S.transitionMorphism φ)).inverseImage ⟶
      (componentMorphism S n).inverseImage :=
  Functor.whiskerRight (S.componentRingedTopos_setRestrictionIso m).hom
      (S.transitionMorphism φ).inverseImage ≫
    S.fiberTransition φ ≫ (S.componentRingedTopos_setRestrictionIso n).inv

/-- The transition of inverse images, with the final comparison of Stacks 09WG cancelled: it is
the inverse image along `f_φ` of that comparison in degree `m`, followed by the inverse-image
transition of Stacks 09WF. -/
theorem componentInverseImageTransition_comp_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf S.totalTopology (Type u)) :
    (S.componentInverseImageTransition φ).app F ≫
        (S.componentRingedTopos_setRestrictionIso n).hom.app F =
      (S.transitionMorphism φ).inverseImage.map
          ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ≫
        (S.fiberTransition φ).app F := by
  have h : (S.componentInverseImageTransition φ).app F =
      (S.transitionMorphism φ).inverseImage.map
          ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ≫
        ((S.fiberTransition φ).app F ≫
          (S.componentRingedTopos_setRestrictionIso n).inv.app F) := rfl
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun q ↦ (S.transitionMorphism φ).inverseImage.map
    ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ≫ q) (Category.comp_id _)

/-- **The 2-morphism `g_n ⟶ g_m ∘ f_φ` of morphisms of topoi.** The mate of
`CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition` under the topos
adjunctions of the component morphisms and of the simplicial transition. -/
def componentPushforwardTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentMorphism S n).pushforward ⟶
      ((componentMorphism S m).comp (S.transitionMorphism φ)).pushforward :=
  conjugateEquiv (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (S.componentInverseImageTransition φ)

variable (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **Stacks 0D72, on structure maps.** The structure map of the component morphism of ringed
topoi `g_n`, read on underlying sheaves of sets, is the adjunct of the comparison of Stacks 09WG
between `g_n⁻¹O` and `O_n`.

Forgetting the ring operations commutes with the hom-set bijection of Stacks 00YV, and the
ring-level comparison of Stacks 0D72 has the set-level comparison of Stacks 09WG underneath. -/
theorem forgetFSharp_componentRingedToposHom (n : SimplexCategory) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (componentRingedToposHom S O n) =
      (componentMorphism S n).adj.homEquiv
        ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)
        ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj
          (S.componentRingedTopos O n).O)
        ((S.componentRingedTopos_setRestrictionIso n).hom.app
          ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) := by
  set G := (sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O
  have hforget : (sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).map
        ((componentRingedTopos_restrictionIso S n).hom.app O) =
      (S.componentRingedTopos_setRestrictionIso n).hom.app G :=
    (componentRingedTopos_restrictionIso_forget S n O).trans
      ((congrArg (fun q ↦ q ≫ (S.componentRingedTopos_setRestrictionIso n).hom.app G)
          (inverseImageCommRingForgetIso_hom_app (S.componentTopology n)
            (componentMorphism S n) O)).trans (Category.id_comp _))
  refine (forget_map_commRingImageAdjunction_homEquiv (componentMorphism S n) O
    (S.componentRingedTopos O n).O
    ((componentRingedTopos_restrictionIso S n).hom.app O)).trans ?_
  exact congrArg ((componentMorphism S n).adj.homEquiv G
      ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj
        (S.componentRingedTopos O n).O)) hforget

/-- **Stacks 04IC for the component morphisms of ringed topoi.** The 2-morphism
`CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition` carries the structure map
of `g_n` to the structure map of `g_m ∘ f_φ`. -/
theorem componentRingedTwoMorphism_commutes {m n : SimplexCategory} (φ : m ⟶ n) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (componentRingedToposHom S O n) ≫
        (S.componentPushforwardTransition φ).app
          ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj
            (S.componentRingedTopos O n).O) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos O n)
          (Y := S.componentRingedTopos O m) (Z := S.totalRingedTopos O)
          (componentRingedToposHom S O m) (S.transitionRingedToposHom O φ)) := by
  set G := (sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O
  have hkey := Stacks.CategoryTheory.homEquiv_conjugate (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (S.componentPushforwardTransition φ) ((S.componentRingedTopos_setRestrictionIso n).hom.app G)
  rw [componentPushforwardTransition, (conjugateEquiv _ _).symm_apply_apply,
    S.componentInverseImageTransition_comp_hom φ G] at hkey
  have hsplit : ((componentMorphism S m).adj.comp (S.transitionMorphism φ).adj).homEquiv G
        ((S.restrict.{u, u} n).obj G)
        ((S.transitionMorphism φ).inverseImage.map
            ((S.componentRingedTopos_setRestrictionIso m).hom.app G) ≫
          (S.fiberTransition φ).app G) =
      (componentMorphism S m).adj.homEquiv G ((S.restrict.{u, u} m).obj G)
          ((S.componentRingedTopos_setRestrictionIso m).hom.app G) ≫
        (componentMorphism S m).pushforward.map ((S.restrictTransition φ).app G) := by
    have hft : (S.transitionMorphism φ).adj.homEquiv
          (((componentFunctor S m).sheafPushforwardContinuous (Type u)
            (S.componentTopology m) S.totalTopology).obj G)
          ((S.restrict.{u, u} n).obj G) ((S.fiberTransition φ).app G) =
        (S.restrictTransition φ).app G :=
      S.fiberTransition_adj φ G
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_left (S.transitionMorphism φ).adj
        ((S.componentRingedTopos_setRestrictionIso m).hom.app G) ((S.fiberTransition φ).app G),
      hft, Adjunction.homEquiv_naturality_right]
    rfl
  refine (congrArg (fun q ↦ q ≫ (S.componentPushforwardTransition φ).app
      ((sheafCompose (S.componentTopology n) (forget CommRingCat.{u})).obj
        (S.componentRingedTopos O n).O))
    (S.forgetFSharp_componentRingedToposHom O n)).trans (hkey.symm.trans ?_)
  refine hsplit.trans ?_
  refine (congrArg (fun q ↦ q ≫ (componentMorphism S m).pushforward.map
      ((S.restrictTransition φ).app G))
    (S.forgetFSharp_componentRingedToposHom O m).symm).trans ?_
  refine (congrArg (fun q ↦ AlgebraicGeometry.RingedToposHom.forgetFSharp
      (componentRingedToposHom S O m) ≫ (componentMorphism S m).pushforward.map q)
    (S.transitionRingedToposHom_forgetFSharp O φ).symm).trans ?_
  exact (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp (componentRingedToposHom S O m)
    (S.transitionRingedToposHom O φ)).symm

/-- **Stacks 04IC for the component morphisms of ringed topoi.** The 2-morphism
`g_n ⟶ g_m ∘ f_φ` of morphisms of *ringed* topoi attached to a simplex map `φ : [m] ⟶ [n]`: the
mate of the inverse-image transition of Stacks 09WF, which is compatible with the structure maps
of the two composites. -/
def componentRingedTwoMorphism {m n : SimplexCategory} (φ : m ⟶ n) :
    AlgebraicGeometry.RingedToposHom.TwoMorphism.{u, u, u, u, u, u}
      (componentRingedToposHom S O n)
      (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos O n)
        (Y := S.componentRingedTopos O m) (Z := S.totalRingedTopos O)
        (componentRingedToposHom S O m) (S.transitionRingedToposHom O φ)) where
  t := S.componentPushforwardTransition φ
  commutes := S.componentRingedTwoMorphism_commutes O φ

section Modules

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotalCartesianModule :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalCartesianModule :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

attribute [local instance] hasWeakSheafifyComponent

/-- **Stacks 09WF, on sheaves of modules.** The transition `f_φ^*F_m ⟶ F_n` between the
component restrictions of a sheaf of `O`-modules on the total site attached to a simplex map
`φ : [m] ⟶ [n]`, restriction to a component being the pullback of sheaves of modules along the
component morphism of ringed topoi of Stacks 0D72.

It is the transformation of pullbacks of sheaves of modules induced by the 2-morphism
`g_n ⟶ g_m ∘ f_φ`, with the pullback along the composite split by the pseudofunctoriality of
Stacks 03D8. -/
def moduleFiberTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRingedToposHom S O m).toModulesHom.pullbackModules ⋙
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ⟶
      (componentRingedToposHom S O n).toModulesHom.pullbackModules :=
  (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).inv ≫
    (S.componentRingedTwoMorphism O φ).pullbackModulesMap

/-- **The cartesian condition of Stacks 07TF for sheaves of modules**, expressed through the
2-morphism of this file: a sheaf of `O`-modules on the total site of a simplicial site is
cartesian when every canonical transition `f_φ^*F_m ⟶ F_n` between its component restrictions,
namely `moduleFiberTransition`, is an isomorphism.

This is part (2) of the source definition; parts (1), (3) and (4) are
`CategoryTheory.SimplicialSiteSituation.IsCartesianSheaf`, `.IsCartesianAbSheaf` and the
derived-category conditions. The same condition stated through the transition of
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition` is
`CategoryTheory.SimplicialSiteSituation.IsCartesianModule`. -/
@[stacks 07TF "part (2), for the module fibre transition of the component 2-morphism"]
abbrev IsModuleFiberTransitionIso
    (F : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) O)) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), IsIso ((S.moduleFiberTransition O φ).app F)

end Modules

end CategoryTheory.SimplicialSiteSituation

end
