module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward

/-!
# The associated module of the structure projection of a morphism of schemes

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism of schemes
`r` is affine, and let `ε_a : (X_étale, 𝒪) ⟶ (Y_étale, 𝒪)` be the morphism of small étale ringed
sites of Stacks 070R (2).  The structure sheaf of `X` carries two canonical morphisms out of the
structure sheaf of `Y`, read as a module over itself:

* on the small **Zariski** sites, the morphism `𝒪_Y ⟶ r_*𝒪_X` of
  `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of `r♯`;
* on the small **étale** sites, the same for
  `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`.

This file proves that the associated-module functor of Stacks 03DU (4) carries the first to the
second, through `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` on the target and
the unit comparison `AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit` on both the source
and the target.

## Main results

* `AlgebraicGeometry.SmallEtale.unitToPushforwardObjUnit_structureMap_square`: the square of
  ringed sites of `ε_a`, read on the structure sheaves as modules — the two routes from `𝒪_Y` on
  the small Zariski site of `Y` to `𝒪_X` on the small étale site of `X` agree.
* `AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso_hom`: the comparison of the
  Zariski restriction of a direct image along `ε_a` with the direct image of the restriction is,
  at one module, the reparametrisation of the composite comparison of structure sheaves.
* `AlgebraicGeometry.SmallEtale.unitToPushforwardObjUnit_comp_restrictModulePushforwardObjIso`:
  that comparison carries the morphism of modules of one composite comparison to the morphism of
  the other.
* `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso_inv`: the inverse of
  `(ε_a)_*(𝓕^a) ≅ (r_*𝓕)^a`, written out.
* `AlgebraicGeometry.SmallEtale.unitToPushforwardObjUnit_toRingCatSheafHom_transpose`: the
  transpose, under the associated-module adjunction, of the main result.
* `AlgebraicGeometry.SmallEtale.associatedModule_map_unitToPushforwardObjUnit_toRingCatSheafHom`:
  **the associated module of the Zariski structure projection is the étale one.**

## Implementation notes

The adjunction of Stacks 03DU (4) is what makes the statement provable at all.  Both sides of the
main result are morphisms out of `(𝒪_Y)^a`, an associated module, so the adjunction turns the
claim into the equality of their transposes — morphisms out of `𝒪_Y` on the small *Zariski* site
of `Y`, which is where the square of ringed sites of `ε_a` is available.  That transpose is
`unitToPushforwardObjUnit_toRingCatSheafHom_transpose`, and the passage between the two is the
counit naturality used twice in the main proof;
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` is by definition the transpose of
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`, so no inverse of a counit is ever
formed.

The two general lemmas of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackUnit.lean` do the work in the
square itself: `AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso` is built from
`CategoryTheory.SheafOfModules.pushforwardComp` at the two corners — which is
`CategoryTheory.Iso.refl`, whence `restrictModulePushforwardObjIso_hom` — and
`CategoryTheory.SheafOfModules.pushforwardCongr₂` in the middle, over the ring half
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso` of the square.

Every step after the square is written as a term — `CategoryTheory.whisker_eq`,
`CategoryTheory.eq_whisker`, `CategoryTheory.Category.assoc` and `congrArg` — rather than by `rw`
or `simp`.  The reason is that the goals mix `AlgebraicGeometry.Scheme.Modules`, whose sheaf of
rings is spelled through `TopCat.Sheaf`, with
`CategoryTheory.SheafOfModules` over the same sheaf of rings spelled through
`CategoryTheory.Sheaf`; the two agree at default transparency but not at the transparency at
which `rw` and `simp` match, so the goals are reported as not type-correct and no rewrite fires.
This is the same obstruction as in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedStructureMapModuleSquare.lean`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-! ### The square of ringed sites on the structure modules -/

/-- **The two routes round the square of ringed sites of `ε_a` carry `𝒪_Y`, read as a module over
itself on the small Zariski site of `Y`, to `𝒪_X` on the small étale site of `X` by the same
morphism.**

This is `AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso` — the ring half of
the square — read on modules: each route is the composite of the morphisms of modules attached to
its two legs, and the comparison of the two direct images attached to
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso` matches them. -/
theorem unitToPushforwardObjUnit_structureMap_square :
    (SheafOfModules.unitToPushforwardObjUnit (structureMap B Y.obj Y.property) ≫
          (SheafOfModules.pushforward.{u} (structureMap B Y.obj Y.property)).map
            (SheafOfModules.unitToPushforwardObjUnit (smallEtaleStructureMapRing B a))) ≫
        (SheafOfModules.pushforwardCongr₂.{u} _ (baseChangeOpensIso B a)
          (structureMap_comp_baseChangeOpensIso B a)).hom.app
          (SheafOfModules.unit (structureSheaf B X.obj X.property)) =
      SheafOfModules.unitToPushforwardObjUnit (schemeHom B a).toRingCatSheafHom ≫
        (SheafOfModules.pushforward.{u} (schemeHom B a).toRingCatSheafHom).map
          (SheafOfModules.unitToPushforwardObjUnit (structureMap B X.obj X.property)) :=
  (congrArg (fun z ↦ z ≫ (SheafOfModules.pushforwardCongr₂.{u} _ (baseChangeOpensIso B a)
        (structureMap_comp_baseChangeOpensIso B a)).hom.app
        (SheafOfModules.unit (structureSheaf B X.obj X.property)))
      (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
        (structureMap B Y.obj Y.property) (smallEtaleStructureMapRing B a))).symm.trans
    ((SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr₂_hom_app _ _ _).trans
      (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp _ _))

/-- The comparison of the Zariski restriction of a direct image along `ε_a` with the direct image
of the Zariski restriction is, at one module, the reparametrisation of the composite comparison of
structure sheaves along `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`: the two corner
identifications of
`AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso` are identities. -/
theorem restrictModulePushforwardObjIso_hom
    (𝓖 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    (restrictModulePushforwardObjIso B a 𝓖).hom =
      (SheafOfModules.pushforwardCongr₂.{u} _ (baseChangeOpensIso B a)
        (structureMap_comp_baseChangeOpensIso B a)).hom.app 𝓖 :=
  (Category.id_comp _).trans (Category.comp_id _)

/-- **The square of direct images carries the morphism of modules of one composite comparison to
the morphism of the other.**  This is
`AlgebraicGeometry.SmallEtale.unitToPushforwardObjUnit_structureMap_square` with both composites
read as single comparisons. -/
theorem unitToPushforwardObjUnit_comp_restrictModulePushforwardObjIso :
    SheafOfModules.unitToPushforwardObjUnit
          (SheafOfModules.comparisonComp (structureMap B Y.obj Y.property)
            (smallEtaleStructureMapRing B a)) ≫
        (restrictModulePushforwardObjIso B a
          (SheafOfModules.unit (structureSheaf B X.obj X.property))).hom =
      SheafOfModules.unitToPushforwardObjUnit
        (SheafOfModules.comparisonComp (schemeHom B a).toRingCatSheafHom
          (structureMap B X.obj X.property)) := by
  rw [restrictModulePushforwardObjIso_hom,
    SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
      (structureMap B Y.obj Y.property) (smallEtaleStructureMapRing B a),
    SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
      ((schemeHom B a).toRingCatSheafHom) (structureMap B X.obj X.property)]
  exact unitToPushforwardObjUnit_structureMap_square B a

/-! ### The associated module of the structure projection -/

/-- The inverse of `(ε_a)_*(𝓕^a) ≅ (r_*𝓕)^a`, written out: the associated module of the
identification of the Zariski restriction of the direct image with `r_*𝓕`, followed by the counit
of the associated-module adjunction of `Y_étale`. -/
theorem pushforwardAssociatedModuleIso_inv [IsAffineHom (schemeHom B a)] (𝓕 : X.obj.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf) 𝓕) :
    (pushforwardAssociatedModuleIso B a 𝓕 h𝓕).inv =
      (associatedModule B Y.obj Y.property).map
          ((Scheme.Modules.pushforward (schemeHom B a)).map
              ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕) ≫
            (restrictModulePushforwardObjIso B a
              ((associatedModule B X.obj X.property).obj 𝓕)).inv) ≫
        (associatedModuleAdjunction B Y.obj Y.property).counit.app _ := by
  simp only [pushforwardAssociatedModuleIso, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
    Iso.symm_inv, asIso_hom]

/-- **The transpose of the main result under the associated-module adjunction of `Y_étale`.**
Both sides are morphisms `𝒪_Y ⟶ (ε_a)_*(𝒪_X)|_{Y_Zar}` of modules on the small Zariski site of
`Y`, and the equality is the square of direct images
`AlgebraicGeometry.SmallEtale.unitToPushforwardObjUnit_comp_restrictModulePushforwardObjIso`
together with the unit of the adjunction of `X_étale` read at the structure sheaf, which is the
transpose of `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`. -/
theorem unitToPushforwardObjUnit_toRingCatSheafHom_transpose :
    SheafOfModules.unitToPushforwardObjUnit (schemeHom B a).toRingCatSheafHom ≫
        ((Scheme.Modules.pushforward (schemeHom B a)).map
            ((associatedModuleAdjunction B X.obj X.property).unit.app
              (SheafOfModules.unit X.obj.ringCatSheaf)) ≫
          (restrictModulePushforwardObjIso B a
            ((associatedModule B X.obj X.property).obj
              (SheafOfModules.unit X.obj.ringCatSheaf))).inv) ≫
        (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
            (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property))) =
      SheafOfModules.unitToPushforwardObjUnit (structureMap B Y.obj Y.property) ≫
        (restrictModule B Y.obj Y.property).map
          (SheafOfModules.unitToPushforwardObjUnit (smallEtaleStructureMapRing B a)) := by
  have hnat := (restrictModulePushforwardSquareIso B a).inv.naturality
    (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property))
  have hunit : (associatedModuleAdjunction B X.obj X.property).unit.app
          (SheafOfModules.unit X.obj.ringCatSheaf) ≫
        (restrictModule B X.obj X.property).map
          (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property)) =
      SheafOfModules.unitToPushforwardObjUnit (structureMap B X.obj X.property) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have inner : ((Scheme.Modules.pushforward (schemeHom B a)).map
            ((associatedModuleAdjunction B X.obj X.property).unit.app
              (SheafOfModules.unit X.obj.ringCatSheaf)) ≫
          (restrictModulePushforwardObjIso B a
            ((associatedModule B X.obj X.property).obj
              (SheafOfModules.unit X.obj.ringCatSheaf))).inv) ≫
        (restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
            (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property))) =
      (Scheme.Modules.pushforward (schemeHom B a)).map
          (SheafOfModules.unitToPushforwardObjUnit (structureMap B X.obj X.property)) ≫
        (restrictModulePushforwardObjIso B a
          (SheafOfModules.unit (structureSheaf B X.obj X.property))).inv := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ hnat.symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg (fun z ↦ (Scheme.Modules.pushforward (schemeHom B a)).map z) hunit)) _
  refine Eq.trans (whisker_eq _ inner) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
      ((schemeHom B a).toRingCatSheafHom) (structureMap B X.obj X.property)).symm _) ?_
  refine Eq.trans (eq_whisker
    (unitToPushforwardObjUnit_comp_restrictModulePushforwardObjIso B a).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Iso.hom_inv_id (restrictModulePushforwardObjIso B a
    (SheafOfModules.unit (structureSheaf B X.obj X.property))))) ?_
  refine Eq.trans (Category.comp_id _) ?_
  exact SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
    (structureMap B Y.obj Y.property) (smallEtaleStructureMapRing B a)

/-- **The associated-module functor of Stacks 03DU (4) carries the Zariski structure projection
`𝒪_Y ⟶ r_*𝒪_X` of a morphism of schemes to the morphism of modules attached to the structure map
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing` of `ε_a`.**

The target is matched by `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`, the
identification `(ε_a)_*(𝒪_X^a) ≅ (r_*𝒪_X)^a` available because `r` is affine and `𝒪_X` is
quasi-coherent, and both ends by
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`, an isomorphism by
`AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`. -/
theorem associatedModule_map_unitToPushforwardObjUnit_toRingCatSheafHom
    [IsAffineHom (schemeHom B a)] :
    (associatedModule B Y.obj Y.property).map
          (SheafOfModules.unitToPushforwardObjUnit (schemeHom B a).toRingCatSheafHom) ≫
        (pushforwardAssociatedModuleIso B a (SheafOfModules.unit X.obj.ringCatSheaf)
          (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.obj)).inv ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
          (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property)) =
      SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B Y.obj Y.property) ≫
        SheafOfModules.unitToPushforwardObjUnit (smallEtaleStructureMapRing B a) := by
  refine Eq.trans (whisker_eq _ (congrArg (fun z ↦ z ≫
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
      (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B X.obj X.property)))
    (pushforwardAssociatedModuleIso_inv B a (SheafOfModules.unit X.obj.ringCatSheaf)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.obj)))) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _).symm _) ?_
  refine Eq.trans (whisker_eq _
    (Adjunction.counit_naturality (associatedModuleAdjunction B Y.obj Y.property) _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun z ↦ (associatedModule B Y.obj Y.property).map z) (Category.assoc _ _ _)) _) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun z ↦ (associatedModule B Y.obj Y.property).map z)
    (unitToPushforwardObjUnit_toRingCatSheafHom_transpose B a)) _) ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (Adjunction.counit_naturality (associatedModuleAdjunction B Y.obj Y.property) _)) ?_
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.SmallEtale

end
