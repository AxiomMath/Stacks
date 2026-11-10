module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleStructureProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealSheafKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedStructureMapModuleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureProjectionChartSquare

/-!
# The structure projection of a representable morphism, carried from the Zariski site

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` whose underlying morphism `r` of schemes is affine.  The scheme `T` carries
the canonical morphism `𝒪_T ⟶ r_*𝒪_{T'}` of modules on its **Zariski** site, and the algebraic
space `yoneda.obj T` carries `AlgebraicGeometry.Space.structureProjectionOfHom` of the represented
morphism, a morphism of modules on its **small étale** site.  This file identifies the second with
the transport of the first along
`AlgebraicGeometry.Space.representedAssociatedModule`.

## Main results

* `AlgebraicGeometry.Space.structureProjectionOfHom_representedSpaceMap`: **the comparison of the
  two direct images of the square of small étale ringed sites carries the morphism of modules
  attached to the structure map of the underlying morphism of schemes to
  `AlgebraicGeometry.Space.structureProjectionOfHom` of the represented morphism.**  This is the
  base square of `RepresentedStructureMapModuleSquare.lean` composed with the chart layer of
  `StructureProjectionChartSquare.lean`.
* `AlgebraicGeometry.Space.representedAssociatedModule_structureProjection_square`: **the
  assembled square** — the transport of the Zariski structure projection of the underlying
  morphism of schemes *is* `AlgebraicGeometry.Space.structureProjectionOfHom` of the represented
  morphism, under `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` at the source
  and `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` followed by
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` at the target.
* `AlgebraicGeometry.Space.representedModulePushforwardSquareIso_hom_app_unit_yoneda` reads the
  comparison of the two direct images at the structure sheaf, and
  `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso_hom_pushforward` writes out the
  identification of the transported structure sheaf with the structure sheaf.

## Implementation notes

The three layers assembled here are

* the **base square**
  `AlgebraicGeometry.Space.unitToPushforwardObjUnit_representedStructureMapRing_square`,
  which reads the square of small étale ringed sites of the represented morphism on the structure
  sheaves as modules;
* the **chart layer**
  `AlgebraicGeometry.Space.structureProjectionOfHom_comp_modulePushforwardChartIso`, which reads
  the canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of Stacks 03LU through base change of étale scheme
  charts;
* the **associated-module layer**
  `AlgebraicGeometry.SmallEtale.associatedModule_map_unitToPushforwardObjUnit_toRingCatSheafHom`,
  which carries the Zariski structure projection of a morphism of schemes to the morphism of
  modules of the morphism of small étale ringed sites.

Two structure comparisons of the square carry no information and are discharged here:
`AlgebraicGeometry.Space.representedEquivSharp` is the identity, so the morphism of modules
attached to it is the identity by `unitToPushforwardObjUnit_representedEquivSharp`, and
`CategoryTheory.SheafOfModules.pushforwardComp` is `CategoryTheory.Iso.refl`, so its two
components in `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` are identities.

Every proof is written as a term — `CategoryTheory.whisker_eq`, `CategoryTheory.eq_whisker`,
`CategoryTheory.Category.assoc` and `congrArg` — and every step is cut into its own declaration.
The reason is the one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedStructureMapModuleSquare.lean`: the goals mix
the
several definitionally equal spellings of the structure sheaf of rings of an algebraic space and
of the scheme underlying an object of the big fppf site, which agree at default transparency but
not at the transparency at which `rw` and `simp` match, so no rewrite fires; and each spelling
change that a step does need is a `whnf` the heartbeat budget only affords once per declaration.
The one place where two spellings of the *object* a natural transformation is read at have to be
matched — the structure sheaf of `yoneda.obj T'` written through the equivalence of the two small
étale sites on one side and through the small étale ringed site on the other — is
`chartIso_inv_app_unit_eq`, closed by `congr 1`, which reduces it to the equality of the two
objects and avoids unfolding the natural transformation.

The witness of relative representability is spelled
`AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map` in the statements that have to meet
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which instantiates that witness
inside itself, and is a hypothesis in the statements that do not.  Which of the two a step needs
is not a matter of taste: the witness is used as *data* downstream, and whichever of the two
spellings a step does not need is a `whnf` it cannot afford.

## What this leaves owed

This is the square, not clause (2) of the conormal statement in the module `Conormal` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection`.
Taking kernels of the two sides is the next step, and it needs one identification this library
does not have: the square is stated for a morphism `g` of the big fppf category over `S`, whereas
`AlgebraicGeometry.Space.definingIdealSheafIsoKernel` presents the defining ideal sheaf of a
*closed subspace* `Z ⊆ yoneda.obj T` as the kernel of
`AlgebraicGeometry.Space.structureProjection`, which is
`AlgebraicGeometry.Space.structureProjectionOfHom` of the inclusion.  What is missing is the
dictionary between the two: an object of the big fppf category over `S` representing `Z`, and the
identification of `AlgebraicGeometry.Space.subspaceInclusion` of `Z` with
`AlgebraicGeometry.Space.representedSpaceMap` of the corresponding morphism.  The representing
closed immersion of schemes is available — it is the base change of `Z ⟶ yoneda.obj T` along the
identity chart, as `AlgebraicGeometry.Space.definingIdealOfHom_obj_selfChart_eq_openChartIdeal`
uses it — but nothing identifies the closed subspace itself with the algebraic space that scheme
represents.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- **The morphism of modules attached to the structure comparison of the identification of the
two small étale sites is the identity.**  That comparison,
`AlgebraicGeometry.Space.representedEquivSharp`, is the identity morphism of sheaves of rings,
and the reading of a comparison on the structure sheaves as modules is its own components with
the ring structure forgotten. -/
theorem unitToPushforwardObjUnit_representedEquivSharp (U : BigFppfOver B S hS) :
    SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS U) = 𝟙 _ := rfl

section Witness

variable (hg : yoneda.relativelyRepresentable (yoneda.map g))

private theorem id_comp_pushforward_map_unit :
    (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (representedSchemeStructureMapRing B S hS g)) =
      SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T) ≫
        (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (representedSchemeStructureMapRing B S hS g)) :=
  Eq.trans (Category.id_comp _).symm
    (eq_whisker (unitToPushforwardObjUnit_representedEquivSharp B S hS T).symm _)

private theorem unitToPushforwardObjUnit_smallBaseChangeSharp_comp_id :
    SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
        (SheafOfModules.pushforward.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).map
          (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) :=
  Eq.trans (whisker_eq _ (CategoryTheory.Functor.map_id _ _)) (Category.comp_id _)

private theorem pushforwardCongr₂_hom_app_unit_comp :
    (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (representedSchemeStructureMapRing B S hS g)) ≫
        (SheafOfModules.pushforwardCongr₂.{u} _
            (representedSmallEtaleBaseChangeIso B S hS g hg)
            (representedStructureMapRing_square B S hS g hg)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) :=
  Eq.trans (eq_whisker (id_comp_pushforward_map_unit B S hS g) _)
    (Eq.trans (unitToPushforwardObjUnit_representedStructureMapRing_square B S hS g hg)
      (unitToPushforwardObjUnit_smallBaseChangeSharp_comp_id B S hS g hg))

private theorem pushforwardComp_symm_hom_app_unit_eq_id :
    (SheafOfModules.pushforwardComp.{u}
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
        (representedEquivSharp B S hS T')).symm.hom.app
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) = 𝟙 _ := rfl

private theorem isoWhiskerLeft_chartIso_hom_app_unit :
    (Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
          (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).symm).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).inv.app
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) := rfl

end Witness

private theorem chartIso_inv_app_unit_eq :
    (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)).inv.app
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)).inv.app
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) := by
  congr 1

private theorem unitToPushforwardObjUnit_comp_chartIso_inv :
    SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)).inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS
            ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) =
      structureProjectionOfHom B S hS (representedSpaceMap B S hS g) :=
  Eq.trans (eq_whisker (structureProjectionOfHom_comp_modulePushforwardChartIso B S hS
      (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)).symm _)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (whisker_eq _ (Iso.hom_inv_id_app _ _)) (Category.comp_id _)))

private theorem glue_aux₁ :
    (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (representedSchemeStructureMapRing B S hS g)) ≫
        ((SheafOfModules.pushforwardCongr₂.{u} _
              (representedSmallEtaleBaseChangeIso B S hS g
                (relativelyRepresentable_yoneda_map B S hS g))
              (representedStructureMapRing_square B S hS g
                (relativelyRepresentable_yoneda_map B S hS g))).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
          (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
              (relativelyRepresentable_yoneda_map B S hS g)).inv.app
            ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))) =
      SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g)) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g)).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  Eq.trans (Category.assoc _ _ _).symm
    (eq_whisker (pushforwardCongr₂_hom_app_unit_comp B S hS g
      (relativelyRepresentable_yoneda_map B S hS g)) _)

private theorem glue_aux₂ :
    SheafOfModules.unitToPushforwardObjUnit
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g)) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g)).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      structureProjectionOfHom B S hS (representedSpaceMap B S hS g) :=
  Eq.trans (whisker_eq _ (chartIso_inv_app_unit_eq B S hS g))
    (unitToPushforwardObjUnit_comp_chartIso_inv B S hS g)

private theorem pushforwardComp_hom_app_unit_eq_id :
    (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g)).hom.app
      (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) = 𝟙 _ := rfl

private theorem squareIso_hom_app_unit_aux :
    (representedModulePushforwardSquareIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
            (representedSchemeStructureMapRing B S hS g)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
        ((SheafOfModules.pushforwardCongr₂.{u} _
              (representedSmallEtaleBaseChangeIso B S hS g
                (relativelyRepresentable_yoneda_map B S hS g))
              (representedStructureMapRing_square B S hS g
                (relativelyRepresentable_yoneda_map B S hS g))).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
          ((SheafOfModules.pushforwardComp.{u}
                (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g)
                  (relativelyRepresentable_yoneda_map B S hS g))
                (representedEquivSharp B S hS T')).symm.hom.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
            (Functor.isoWhiskerLeft
                ((representedSmallEtaleModuleEquivalence B S hS T').functor)
                (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
                  (relativelyRepresentable_yoneda_map B S hS g)).symm).hom.app
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))) := rfl

/-- **The comparison of the two direct images of the square of small étale ringed sites, read at
the structure sheaf.**  Of the four factors of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` the two built from
`CategoryTheory.SheafOfModules.pushforwardComp` are identities, that functor comparison being
`CategoryTheory.Iso.refl`, so the comparison is the reparametrisation along the identification of
the two base changes followed by the inverse of the chart comparison of the direct image. -/
theorem representedModulePushforwardSquareIso_hom_app_unit_yoneda :
    (representedModulePushforwardSquareIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      (SheafOfModules.pushforwardCongr₂.{u} _
            (representedSmallEtaleBaseChangeIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g))
            (representedStructureMapRing_square B S hS g
              (relativelyRepresentable_yoneda_map B S hS g))).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) ≫
        (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g)
            (relativelyRepresentable_yoneda_map B S hS g)).inv.app
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) :=
  (squareIso_hom_app_unit_aux B S hS g).trans
    (Eq.trans (eq_whisker (pushforwardComp_hom_app_unit_eq_id B S hS g) _)
      (Eq.trans (Category.id_comp _)
        (whisker_eq _ (Eq.trans (eq_whisker (pushforwardComp_symm_hom_app_unit_eq_id B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)) _)
          (Eq.trans (Category.id_comp _)
            (isoWhiskerLeft_chartIso_hom_app_unit B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)))))))

/-- **The square of small étale ringed sites carries the morphism of modules attached to the
structure map of the underlying morphism of schemes to the canonical morphism
`𝒪_Y ⟶ f_*𝒪_X` of the represented morphism.**

This is the base square of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedStructureMapModuleSquare.lean` composed with the
chart layer of `StacksFrontier/AlgebraicGeometry/Spaces/StructureProjectionChartSquare.lean`: the
first identifies the two routes round the square on the structure sheaves as modules, the second
identifies the route through base change of charts with `𝒪_Y ⟶ f_*𝒪_X` itself. -/
theorem structureProjectionOfHom_representedSpaceMap :
    (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (representedSchemeStructureMapRing B S hS g)) ≫
        (representedModulePushforwardSquareIso B S hS g
            (relativelyRepresentable_yoneda_map B S hS g)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      structureProjectionOfHom B S hS (representedSpaceMap B S hS g) :=
  Eq.trans (whisker_eq _ (representedModulePushforwardSquareIso_hom_app_unit_yoneda B S hS g))
    (Eq.trans (glue_aux₁ B S hS g) (glue_aux₂ B S hS g))

/-- The identification of the transported structure sheaf of the representing scheme with the
structure sheaf of the small étale site of the algebraic space it represents, written out: it is
the transport of the unit comparison of the associated-module adjunction, the identification of
the transported structure sheaf being `CategoryTheory.Iso.refl`. -/
theorem representedAssociatedModuleObjUnitIso_hom_pushforward (U : BigFppfOver B S hS)
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    (representedAssociatedModuleObjUnitIso B S hS U hF).hom =
      (representedModulePushforward B S hS U).map
        (SheafOfModules.pullbackObjUnitToUnit.{u}
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) :=
  Category.comp_id _

section Assembly

variable [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)]

omit [_root_.AlgebraicGeometry.IsAffineHom
  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)] in
private theorem representedAssociatedModule_map_eq :
    (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
        (SheafOfModules.unitToPushforwardObjUnit
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            g.left).toRingCatSheafHom) =
      (representedModulePushforward B S hS T).map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          (SheafOfModules.unitToPushforwardObjUnit
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toRingCatSheafHom)) := rfl

open _root_.AlgebraicGeometry.SmallEtale in
/-- **The assembled square: the transport of the Zariski structure projection of the underlying
morphism of schemes is the structure projection of the represented morphism of algebraic
spaces.**

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism `r` of
schemes is affine.  The functor `AlgebraicGeometry.Space.representedAssociatedModule` carries the
canonical morphism `𝒪_T ⟶ r_*𝒪_{T'}` of modules on the Zariski site of `T` to
`AlgebraicGeometry.Space.structureProjectionOfHom` of the represented morphism, under the
identification `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` of the source and
the identification of the target by
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` — available because `r` is affine
and `𝒪_{T'}` is quasi-coherent — read through
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` and then transported by
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`. -/
theorem representedAssociatedModule_structureProjection_square :
    (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).map
          (SheafOfModules.unitToPushforwardObjUnit
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left).toRingCatSheafHom) ≫
        ((representedModulePushforward B S hS T).map
            ((_root_.AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso
                  (associatedBigEtaleSite B) g.left
                  (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf)
                  (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
                    ((BigFppfOver.toScheme B S hS).obj T'))).inv ≫
              (SheafOfModules.pushforward.{u}
                  (representedSchemeStructureMapRing B S hS g)).map
                (SheafOfModules.pullbackObjUnitToUnit.{u}
                  (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))) ≫
          (representedModulePushforwardSquareIso B S hS g
              (relativelyRepresentable_yoneda_map B S hS g)).hom.app
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T'))) =
      (representedAssociatedModuleObjUnitIso B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).hom ≫
        structureProjectionOfHom B S hS (representedSpaceMap B S hS g) := by
  refine Eq.trans (eq_whisker (representedAssociatedModule_map_eq B S hS g) _) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _).symm _) ?_
  have hlayer : _ = _ :=
    associatedModule_map_unitToPushforwardObjUnit_toRingCatSheafHom
      (associatedBigEtaleSite B) g.left
  refine Eq.trans (eq_whisker (congrArg
    (fun z ↦ (representedModulePushforward B S hS T).map z) hlayer) _) ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (structureProjectionOfHom_representedSpaceMap B S hS g)) ?_
  exact eq_whisker
    (representedAssociatedModuleObjUnitIso_hom_pushforward B S hS T
      (isAlgebraicSpace_yoneda B S hS T)).symm _

end Assembly

end AlgebraicGeometry.Space

end
