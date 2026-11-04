module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# `π_!` on sheaves of modules is the colimit over `Δᵒᵖ`

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it and let `π : Δ × C ⥤ C` be the
projection of Stacks 09D0. `StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/
SimplicialModuleEquivalence.lean` identifies sheaves of `π^{-1}O`-modules on `Δ × C` with
simplicial sheaves of `O`-modules on `C`. This file reads off from that equivalence the
description of the lower shriek of `π` on sheaves of modules that Stacks 09D0 asserts:

`π_! = fibrewiseMod ⋙ colim`.

It is the module-coefficient form of
`Stacks.SimplicialModules.abelianLowerShriekIsoColim`, and the proof is the same: the
equivalence, the adjunction `colim ⊣ const` on simplicial objects and the identification of
restriction along `π`, read fibrewise, with the constant simplicial module together exhibit
`fibrewiseMod ⋙ colim` as a left adjoint of restriction along `π`; the lower shriek `π_!` is
another, and left adjoints of one functor agree.

## Main results

* `Stacks.SimplicialModules.fibrewiseModCompRestrictionIso`: reading restriction along `π`
  fibrewise gives the constant simplicial sheaf of modules.
* `Stacks.SimplicialModules.constCompUncurryModIso`: the right adjoint of
  `fibrewiseMod ⋙ colim` is restriction along `π`.
* `Stacks.SimplicialModules.moduleLowerShriekIsoColim`: **`π_!` on sheaves of modules is the
  colimit over `Δᵒᵖ`.**

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]

/-- **`fibrewiseMod` is an equivalence of categories**: it is the functor of
`Stacks.SimplicialModules.simplicialModuleEquivalence`. -/
instance isEquivalence_fibrewiseMod : (fibrewiseMod C J O).IsEquivalence :=
  (simplicialModuleEquivalence C J O).isEquivalence_functor

/-- `fibrewiseMod` is a left adjoint, being half of an equivalence. -/
instance isLeftAdjoint_fibrewiseMod : (fibrewiseMod C J O).IsLeftAdjoint :=
  (simplicialModuleEquivalence C J O).toAdjunction.isLeftAdjoint

/-- `fibrewiseMod` preserves zero morphisms, being a left adjoint between preadditive
categories. -/
instance preservesZeroMorphisms_fibrewiseMod :
    (fibrewiseMod C J O).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- `fibrewiseMod` is additive: it is an equivalence, hence preserves binary coproducts, hence
binary biproducts, the source and target being preadditive with biproducts. -/
instance additive_fibrewiseMod : (fibrewiseMod C J O).Additive :=
  haveI : PreservesBinaryBiproducts (fibrewiseMod C J O) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- `fibrewiseMod` preserves homology, being an equivalence: it preserves all kernels and all
cokernels. -/
instance preservesHomology_fibrewiseMod : (fibrewiseMod C J O).PreservesHomology where

/-- **Reading restriction along `π` fibrewise gives the constant simplicial sheaf of modules.**
The fibre inclusion `i_n` followed by `π` is the identity, so every component is the identity on
sections, and the structure maps of the simplicial module are restrictions of `N` along
identities. -/
def fibrewiseModCompRestrictionIso :
    restrictionModules (projectionTopology C J) J (projection C) O ⋙ fibrewiseMod C J O ≅
      CategoryTheory.Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents
    (fun N => NatIso.ofComponents
      (fun _ => (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {_ _} _ => rfl)))
      (fun {_ n} α => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun U => ?_))
        refine ModuleCat.hom_ext
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
        change N.val.presheaf.map (𝟙 U) x = x
        rw [CategoryTheory.Functor.map_id]
        rfl))
    (fun {_ _} _ => by
      refine NatTrans.ext (funext fun _ => ?_)
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun _ => ?_))
      refine ModuleCat.hom_ext
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun _ => ?_))
      rfl)

/-- **The right adjoint of `fibrewiseMod ⋙ colim` is restriction along `π`**: it is
`Functor.const ⋙ uncurryMod` by the adjunctions, and that is restriction along `π` by
`Stacks.SimplicialModules.fibrewiseModCompRestrictionIso` together with the equivalence. -/
def constCompUncurryModIso :
    CategoryTheory.Functor.const SimplexCategoryᵒᵖ ⋙ uncurryMod C J O ≅
      restrictionModules (projectionTopology C J) J (projection C) O :=
  ((Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (fibrewiseModUncurryIso C J O) ≪≫
    Functor.isoWhiskerRight (fibrewiseModCompRestrictionIso C J O)
      (uncurryMod C J O)).symm

variable [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O)]

/-- **Stacks 09D0 at module coefficients, the lower shriek.** `π_!` on sheaves of modules is the
colimit over `Δᵒᵖ` of the simplicial sheaf of modules that a sheaf of `π^{-1}O`-modules on
`Δ × C` is.

Both sides are left adjoints of restriction along `π`: the left-hand side by
`Stacks.Cohomology.DerivedLowerShriek.adjunctionModules`, and the right-hand side because
`fibrewiseMod` is an equivalence, `colim` is left adjoint to the constant simplicial module, and
the composite right adjoint is restriction along `π` by
`Stacks.SimplicialModules.constCompUncurryModIso`. -/
def moduleLowerShriekIsoColim :
    lowerShriekModules (projectionTopology C J) J (projection C) O ≅
      fibrewiseMod C J O ⋙
        (colim : (SimplexCategoryᵒᵖ ⥤ SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O) :=
  Adjunction.leftAdjointUniq
    (adjunctionModules (projectionTopology C J) J (projection C) O)
    (((simplicialModuleEquivalence C J O).toAdjunction.comp colimConstAdj).ofNatIsoRight
      (constCompUncurryModIso C J O))

end Stacks.SimplicialModules

end
