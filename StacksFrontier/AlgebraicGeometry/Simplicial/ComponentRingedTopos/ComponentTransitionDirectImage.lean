module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackUnderlying
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The transition of component modules in direct-image form, transposed

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`φ : [m] ⟶ [n]` a simplex map. This file proves the identity of *direct images* that compares the
2-morphism `g_n ⟶ g_m ∘ f_φ` of Stacks 04IC with the direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransitionModulesApp` of Stacks 09WF, both read
against the unit of the pullback–pushforward adjunction of Stacks 03D7 and transported along the
comparison of Stacks 0D72 between the two presentations of restriction to a component.

It is a statement about sheaves of sets: the direct images of sheaves of modules have the direct
images of the underlying sheaves of sets underneath, the 2-morphism *is* the 2-morphism of topoi
on them, and the comparison of Stacks 0D72 is the comparison of Stacks 09WG by
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso_underlying`. So
the content is the corresponding identity for sheaves of sets, which is the computation inside
`CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism_commutes` performed at an
arbitrary sheaf of sets instead of at the structure sheaf.

## Main results

* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_unit_comp_pushforwardModules_map`: the
  unit of Stacks 03D7 followed by the direct image of a comparison of the pullback of modules
  with another functor is, on underlying sheaves of sets, the adjunct of that comparison's
  underlying morphism.
* `AlgebraicGeometry.RingedToposHom.unit_comp_pushforwardModulesMap_comp_compIso`: consequently
  the identity of direct images of modules follows from the identity of sheaves of sets, for an
  arbitrary 2-morphism of morphisms of ringed topoi with invertible structure maps.
* `CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition_adjunct`: **the
  sheaf-of-sets identity.** At an arbitrary sheaf of sets the adjunct of the comparison of
  Stacks 09WG followed by the 2-morphism of Stacks 04IC is the adjunct in degree `m` followed by
  the direct image of the transition of Stacks 09WF.
* `CategoryTheory.SimplicialSiteSituation.componentPushforwardModulesMap_adjunct`: **the
  statement**, for sheaves of modules.

## Implementation notes

The two general statements are proved at an abstract morphism of ringed topoi, and at an abstract
comparison of the pullback of modules with a functor, because at the concrete component morphisms
the elaborator has to identify the underlying sheaf of a direct image of modules along a
composite with a composite of direct images of sheaves of sets, and although that holds by
`Eq.refl` it is expensive there. With the morphisms as variables the identification is free, and
the instance at the component morphisms is obtained by applying the general statement.

The sheaf-of-sets identity is `Stacks.CategoryTheory.homEquiv_conjugate` at the 2-morphism of
Stacks 04IC — whose conjugate is the inverse-image transition by construction — followed by
`CategoryTheory.SimplicialSiteSituation.componentInverseImageTransition_comp_hom` and the
splitting of the adjunction of a composite morphism of topoi, exactly as in
`componentRingedTwoMorphism_commutes`.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The unit of Stacks 03D7 transported along a comparison of the pullback of modules, on
underlying sheaves of sets.** For a morphism of ringed topoi with invertible structure map and a
comparison `ι` of its pullback of modules with a functor `R`, the unit followed by the direct
image of `ι` is, on underlying sheaves of sets, the adjunct of the underlying morphism of `ι`
read through
`AlgebraicGeometry.RingedToposHom.pullbackUnderlyingIsoOfIsIso`.

The unit is given on underlying sheaves of sets by
`moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app` and the direct image by
`moduleSheafFunctor_map_pushforwardModules_map`; the hypothesis names the value of the remaining
composite. -/
theorem moduleSheafFunctor_map_unit_comp_pushforwardModules_map (f : RingedToposHom X Y)
    [IsIso f.fSharpInverseImage]
    {R : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (ι : f.toModulesHom.pullbackModules ≅ R)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    {v : f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ⟶
      Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
        (R.obj M)}
    (hv : (pullbackUnderlyingIsoOfIsIso f).inv.app M ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map (ι.hom.app M) = v) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        (f.pullbackAdjPushforwardModules.unit.app M ≫
          f.pushforwardModules.map (ι.hom.app M)) =
      f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) M) ≫
        f.toToposHom.pushforward.map v := by
  refine (Functor.map_comp _ _ _).trans ((congrArg₂ (· ≫ ·)
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f M)
    (moduleSheafFunctor_map_pushforwardModules_map f (ι.hom.app M))).trans ?_)
  exact (Category.assoc _ _ _).trans
    (congrArg _ ((f.toToposHom.pushforward.map_comp _ _).symm.trans (congrArg _ hv)))

/-- **The identity of direct images of sheaves of modules follows from the identity of sheaves of
sets.** Let `g_n : X ⟶ Z` and `g_m : Y ⟶ Z` have invertible structure maps, let `f : X ⟶ Y` and
let `t : g_n ⟶ g_m ∘ f` be a 2-morphism. Given comparisons `ι_n`, `ι_m` of the two pullbacks of
modules with functors `R_n`, `R_m` and a map `w : R_m M ⟶ f_* (R_n M)`, the unit of Stacks 03D7
transported along `ι_n` followed by `t` and the compositor of Stacks 03D8 is the unit
transported along `ι_m` followed by the direct image of `w`, as soon as the corresponding
identity of sheaves of sets holds.

A morphism of sheaves of modules is determined by its underlying morphism of sheaves of sets;
there the two units are given by
`moduleSheafFunctor_map_unit_comp_pushforwardModules_map`, the transformation of direct images
induced by the 2-morphism *is* the 2-morphism
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap`),
and the compositor is the identity. -/
theorem unit_comp_pushforwardModulesMap_comp_compIso (f : RingedToposHom X Y)
    (gm : RingedToposHom Y Z) (gn : RingedToposHom X Z)
    [IsIso gm.fSharpInverseImage] [IsIso gn.fSharpInverseImage]
    (t : TwoMorphism gn (gm.comp f))
    {Rn : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (ιn : gn.toModulesHom.pullbackModules ≅ Rn)
    {Rm : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))}
    (ιm : gm.toModulesHom.pullbackModules ≅ Rm)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
    (w : Rm.obj M ⟶ f.pushforwardModules.obj (Rn.obj M))
    {vn : gn.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M) ⟶
      Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))
        (Rn.obj M)}
    {vm : gm.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M) ⟶
      Sheaf.moduleSheaf.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))
        (Rm.obj M)}
    (hvn : (pullbackUnderlyingIsoOfIsIso gn).inv.app M ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map (ιn.hom.app M) = vn)
    (hvm : (pullbackUnderlyingIsoOfIsIso gm).inv.app M ≫
        (Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map (ιm.hom.app M) = vm)
    (hset : (gn.toToposHom.adj.unit.app
              (Sheaf.moduleSheaf.{u, u, u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M) ≫
            gn.toToposHom.pushforward.map vn) ≫
          t.t.app (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) (Rn.obj M)) =
        (gm.toToposHom.adj.unit.app
              (Sheaf.moduleSheaf.{u, u, u}
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) M) ≫
            gm.toToposHom.pushforward.map vm) ≫
          gm.toToposHom.pushforward.map
            ((Sheaf.moduleSheafFunctor
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map w)) :
    (gn.pullbackAdjPushforwardModules.unit.app M ≫
          gn.pushforwardModules.map (ιn.hom.app M)) ≫
        (t.pushforwardModulesMap.app (Rn.obj M) ≫
          (pushforwardModulesCompIso f gm).hom.app (Rn.obj M)) =
      (gm.pullbackAdjPushforwardModules.unit.app M ≫
            gm.pushforwardModules.map (ιm.hom.app M)) ≫
        gm.pushforwardModules.map w := by
  have e2 : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
        (t.pushforwardModulesMap.app (Rn.obj M) ≫
          (pushforwardModulesCompIso f gm).hom.app (Rn.obj M)) =
      t.t.app (Sheaf.moduleSheaf.{u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) (Rn.obj M)) :=
    rfl
  refine hom_ext_moduleSheafFunctor ?_
  refine Eq.trans (Functor.map_comp _ _ _) (Eq.trans ?_ (Functor.map_comp _ _ _).symm)
  refine (congrArg₂ (· ≫ ·)
    (moduleSheafFunctor_map_unit_comp_pushforwardModules_map gn ιn M hvn) e2).trans
    (hset.trans (congrArg₂ (· ≫ ·)
      (moduleSheafFunctor_map_unit_comp_pushforwardModules_map gm ιm M hvm)
      (moduleSheafFunctor_map_pushforwardModules_map gm w)).symm)

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n)

/-- **Stacks 04IC against Stacks 09WF, for sheaves of sets.** At an arbitrary sheaf of sets on the
total site, the adjunct of the comparison of Stacks 09WG in degree `n` followed by the 2-morphism
`g_n ⟶ g_m ∘ f_φ` is the adjunct of the comparison in degree `m` followed by the direct image of
the transition of Stacks 09WF.

This is the computation inside
`CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism_commutes`, which is this
statement at the underlying sheaf of sets of the structure sheaf, performed at an arbitrary sheaf
of sets: the 2-morphism is the conjugate of the inverse-image transition, so
`Stacks.CategoryTheory.homEquiv_conjugate` moves it to the other side of the adjunction, where
`componentInverseImageTransition_comp_hom` identifies it and the adjunction of the composite
morphism of topoi splits. -/
@[sga "4 VI 7.4.5" "special case"]
theorem componentPushforwardTransition_adjunct (F : Sheaf S.totalTopology (Type u)) :
    ((componentMorphism S n).adj.unit.app F ≫
          (componentMorphism S n).pushforward.map
            ((S.componentRingedTopos_setRestrictionIso n).hom.app F)) ≫
        (S.componentPushforwardTransition φ).app ((S.restrict.{u, u} n).obj F) =
      ((componentMorphism S m).adj.unit.app F ≫
          (componentMorphism S m).pushforward.map
            ((S.componentRingedTopos_setRestrictionIso m).hom.app F)) ≫
        (componentMorphism S m).pushforward.map ((S.restrictTransition φ).app F) := by
  rw [← Adjunction.homEquiv_unit (componentMorphism S n).adj F _
      ((S.componentRingedTopos_setRestrictionIso n).hom.app F),
    ← Adjunction.homEquiv_unit (componentMorphism S m).adj F _
      ((S.componentRingedTopos_setRestrictionIso m).hom.app F)]
  have hconj : (conjugateEquiv (componentMorphism S n).adj
        ((componentMorphism S m).comp (S.transitionMorphism φ)).adj).symm
      (S.componentPushforwardTransition φ) = S.componentInverseImageTransition φ :=
    (conjugateEquiv (componentMorphism S n).adj
      ((componentMorphism S m).comp (S.transitionMorphism φ)).adj).symm_apply_apply _
  have hkey := Stacks.CategoryTheory.homEquiv_conjugate (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (S.componentPushforwardTransition φ)
    ((S.componentRingedTopos_setRestrictionIso n).hom.app F)
  rw [hconj, S.componentInverseImageTransition_comp_hom φ F] at hkey
  have hsplit : ((componentMorphism S m).adj.comp (S.transitionMorphism φ).adj).homEquiv F
        ((S.restrict.{u, u} n).obj F)
        ((S.transitionMorphism φ).inverseImage.map
            ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ≫
          (S.fiberTransition φ).app F) =
      (componentMorphism S m).adj.homEquiv F ((S.restrict.{u, u} m).obj F)
          ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ≫
        (componentMorphism S m).pushforward.map ((S.restrictTransition φ).app F) := by
    have hft : (S.transitionMorphism φ).adj.homEquiv
          (((componentFunctor S m).sheafPushforwardContinuous (Type u)
            (S.componentTopology m) S.totalTopology).obj F)
          ((S.restrict.{u, u} n).obj F)
          ((S.fiberTransition φ).app F) =
        (S.restrictTransition φ).app F :=
      S.fiberTransition_adj φ F
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_left (S.transitionMorphism φ).adj
        ((S.componentRingedTopos_setRestrictionIso m).hom.app F)
        ((S.fiberTransition φ).app F),
      hft]
    exact Adjunction.homEquiv_naturality_right (componentMorphism S m).adj
      ((S.componentRingedTopos_setRestrictionIso m).hom.app F) ((S.restrictTransition φ).app F)
  exact hkey.symm.trans hsplit


variable (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The unit of the topos adjunction of `g_k` against the comparison of Stacks 09WG, in the two
spellings of the component morphism of topoi that the ringed topos and the simplicial situation
give it. -/
private theorem componentRingedToposHom_adj_unit_comp (k : SimplexCategory)
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (componentRingedToposHom S O k).toToposHom.adj.unit.app
          (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
        (componentRingedToposHom S O k).toToposHom.pushforward.map
          ((componentRingedTopos_setRestrictionIso S k).hom.app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) =
      (componentMorphism S k).adj.unit.app
          (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ≫
        (componentMorphism S k).pushforward.map
          ((componentRingedTopos_setRestrictionIso S k).hom.app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  rfl

/-- The 2-morphism of ringed topoi of Stacks 04IC is the 2-morphism of topoi it is built from,
at the underlying sheaf of sets of a restricted module. -/
private theorem componentRingedTwoMorphism_t_app_moduleSheaf
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (S.componentRingedTwoMorphism O φ).t.app
        (Sheaf.moduleSheaf.{u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (S.componentRingedTopos O n).J) (S.componentRingedTopos O n).O))
          ((S.componentModulesRestriction O n).obj M)) =
      (S.componentPushforwardTransition φ).app
        ((S.restrict.{u, u} n).obj (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  rfl

/-- The underlying morphism of the direct-image transition of modules is the direct-image
transition of sheaves of sets. -/
private theorem moduleSheafFunctor_map_restrictTransitionModulesApp
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (S.componentRingedTopos O m).J) (S.componentRingedTopos O m).O))).map
        (S.restrictTransitionModulesApp O φ M) =
      (S.restrictTransition φ).app
        (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) :=
  rfl

/-- The direct image of the direct-image transition of sheaves of sets, in the two spellings of
the component morphism of topoi. -/
private theorem pushforward_map_restrictTransition_app
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (componentRingedToposHom S O m).toToposHom.pushforward.map
        ((S.restrictTransition φ).app
          (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) =
      (componentMorphism S m).pushforward.map
        ((S.restrictTransition φ).app
          (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  rfl

/-- The left-hand side of `componentPushforwardTransition_adjunct` at the underlying sheaf of
sets of a sheaf of modules, in the spelling the module-level statement produces. -/
private theorem componentPushforwardTransition_adjunct_lhs
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((componentRingedToposHom S O n).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O n).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S n).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (S.componentRingedTwoMorphism O φ).t.app
          (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.componentRingedTopos O n).J) (S.componentRingedTopos O n).O))
            ((S.componentModulesRestriction O n).obj M)) =
      ((componentMorphism S n).adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ≫
          (componentMorphism S n).pushforward.map
            ((componentRingedTopos_setRestrictionIso S n).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (S.componentPushforwardTransition φ).app
          ((S.restrict.{u, u} n).obj
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  congrArg₂ (fun x y => x ≫ y) (S.componentRingedToposHom_adj_unit_comp O n M)
    (S.componentRingedTwoMorphism_t_app_moduleSheaf φ O M)

/-- The right-hand side of `componentPushforwardTransition_adjunct`, with the direct-image
transition of modules replaced by the direct-image transition of sheaves of sets. -/
private theorem componentPushforwardTransition_adjunct_rhs_step
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((componentRingedToposHom S O m).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O m).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S m).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (componentRingedToposHom S O m).toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.componentRingedTopos O m).J) (S.componentRingedTopos O m).O))).map
            (S.restrictTransitionModulesApp O φ M)) =
      ((componentRingedToposHom S O m).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O m).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S m).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (componentRingedToposHom S O m).toToposHom.pushforward.map
          ((S.restrictTransition φ).app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  congrArg
    (fun q => ((componentRingedToposHom S O m).toToposHom.adj.unit.app
          (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
        (componentRingedToposHom S O m).toToposHom.pushforward.map
          ((componentRingedTopos_setRestrictionIso S m).hom.app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
      (componentRingedToposHom S O m).toToposHom.pushforward.map q)
    (S.moduleSheafFunctor_map_restrictTransitionModulesApp φ O M)

/-- The right-hand side of `componentPushforwardTransition_adjunct` at the underlying sheaf of
sets of a sheaf of modules, in the spelling the module-level statement produces. -/
private theorem componentPushforwardTransition_adjunct_rhs
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((componentRingedToposHom S O m).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O m).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S m).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (componentRingedToposHom S O m).toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.componentRingedTopos O m).J) (S.componentRingedTopos O m).O))).map
            (S.restrictTransitionModulesApp O φ M)) =
      ((componentMorphism S m).adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) ≫
          (componentMorphism S m).pushforward.map
            ((componentRingedTopos_setRestrictionIso S m).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (componentMorphism S m).pushforward.map
          ((S.restrictTransition φ).app
            (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) :=
  (S.componentPushforwardTransition_adjunct_rhs_step φ O M).trans
    (congrArg₂ (fun x y => x ≫ y) (S.componentRingedToposHom_adj_unit_comp O m M)
      (S.pushforward_map_restrictTransition_app φ O M))

/-- `componentPushforwardTransition_adjunct` at the underlying sheaf of sets of a sheaf of
modules, spelled as the sheaf-of-sets hypothesis of
`AlgebraicGeometry.RingedToposHom.unit_comp_pushforwardModulesMap_comp_compIso` asks for it. -/
private theorem componentPushforwardTransition_adjunct_moduleSheaf
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((componentRingedToposHom S O n).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O n).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S n).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (S.componentRingedTwoMorphism O φ).t.app
          (Sheaf.moduleSheaf.{u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.componentRingedTopos O n).J) (S.componentRingedTopos O n).O))
            ((S.componentModulesRestriction O n).obj M)) =
      ((componentRingedToposHom S O m).toToposHom.adj.unit.app
            (Sheaf.moduleSheaf.{u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (J := (S.totalRingedTopos O).J) (S.totalRingedTopos O).O)) M) ≫
          (componentRingedToposHom S O m).toToposHom.pushforward.map
            ((componentRingedTopos_setRestrictionIso S m).hom.app
              (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) ≫
        (componentRingedToposHom S O m).toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (S.componentRingedTopos O m).J) (S.componentRingedTopos O m).O))).map
            (S.restrictTransitionModulesApp O φ M)) :=
  (S.componentPushforwardTransition_adjunct_lhs φ O M).trans
    ((S.componentPushforwardTransition_adjunct φ
        (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)).trans
      (S.componentPushforwardTransition_adjunct_rhs φ O M).symm)

/-- **Stacks 04IC against Stacks 09WF, for sheaves of modules.** The unit of the adjunction of
Stacks 03D7 for `g_n`, transported along the comparison of Stacks 0D72 and followed by the
2-morphism of Stacks 04IC on direct images of modules and the compositor of Stacks 03D8, is the
unit for `g_m` transported along the comparison of Stacks 0D72 and followed by the direct image
of the transition of Stacks 09WF.

It is `AlgebraicGeometry.RingedToposHom.unit_comp_pushforwardModulesMap_comp_compIso` at the
component morphisms of ringed topoi, whose two comparison hypotheses are
`componentPullbackModulesRestrictionIso_underlying` and whose sheaf-of-sets hypothesis is
`componentPushforwardTransition_adjunct`. -/
theorem componentPushforwardModulesMap_adjunct (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    ((componentRingedToposHom S O n).pullbackAdjPushforwardModules.unit.app M ≫
          (componentRingedToposHom S O n).pushforwardModules.map
            ((componentPullbackModulesRestrictionIso S O n).hom.app M)) ≫
        ((S.componentRingedTwoMorphism O φ).pushforwardModulesMap.app
            ((S.componentModulesRestriction O n).obj M) ≫
          (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso
              (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).hom.app
            ((S.componentModulesRestriction O n).obj M)) =
      ((componentRingedToposHom S O m).pullbackAdjPushforwardModules.unit.app M ≫
            (componentRingedToposHom S O m).pushforwardModules.map
              ((componentPullbackModulesRestrictionIso S O m).hom.app M)) ≫
        (componentRingedToposHom S O m).pushforwardModules.map
          (S.restrictTransitionModulesApp O φ M) :=
  AlgebraicGeometry.RingedToposHom.unit_comp_pushforwardModulesMap_comp_compIso
    (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)
    (componentRingedToposHom S O n) (S.componentRingedTwoMorphism O φ)
    (componentPullbackModulesRestrictionIso S O n)
    (componentPullbackModulesRestrictionIso S O m) M (S.restrictTransitionModulesApp O φ M)
    (S.componentPullbackModulesRestrictionIso_underlying O n M)
    (S.componentPullbackModulesRestrictionIso_underlying O m M)
    (S.componentPushforwardTransition_adjunct_moduleSheaf φ O M)

end CategoryTheory.SimplicialSiteSituation

end
