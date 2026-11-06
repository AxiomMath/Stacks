module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars

/-!
# The direct image of modules along a representable morphism, on underlying sheaves of sets

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  Two direct images of `𝒪_X`-modules are available for such an `f`: the
direct image `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU, which carries the ring
and module operations across the comparison equivalence of Stacks 03G1 and restricts scalars
along the structure map `f♯` of Stacks 03G8, and the direct image
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which is restriction of scalars
along base change of étale scheme charts.  They are identified by
`AlgebraicGeometry.Space.modulePushforwardChartIso`.

This file shows that the identification is nothing but the comparison of the direct images of
*sheaves of sets* with a module structure carried along it: on underlying sheaves of sets it is
`AlgebraicGeometry.Space.chartComparison`, and over an étale scheme chart `V` of `Y` it is the
projection of the limit of chart sections to the base-changed chart `V ×_Y X`.  So for a
representable morphism the direct image of modules of Stacks 03LU has the sections one expects —
the sections of the module over `V ×_Y X` — and the comparison does not move them.

## Main results

* `AlgebraicGeometry.Space.moduleSheaf_smallBaseChangeModulePushforward`: the sheaf of sets
  underlying the chart direct image of an `𝒪_X`-module is the restriction, along base change of
  charts, of the sheaf of sets underlying the module.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardChartIso_hom_app`: **the
  comparison of the two direct images of modules is, on underlying sheaves of sets, the
  comparison of the direct images of sheaves of sets.**
* `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app_apply`: the same comparison
  on sections over an étale scheme chart `V` of `Y`, as the projection of the limit of chart
  sections to the base-changed chart `V ×_Y X`.
* `Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_restrictionModuleIso_hom_app`: the
  identification of the inverse image of modules along the restriction functor of a continuous
  functor of sites with restriction itself is the identity on underlying sheaves of sets.
* `Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp`: the
  transport of the inverse image of modules along a natural transformation to that restriction
  functor, followed by that identification, is the transformation itself on underlying sheaves
  of sets.

## Implementation notes

`AlgebraicGeometry.Space.modulePushforwardChartIso` is assembled from three steps: the transport
of the inverse image of modules along the comparison of the two direct images of sheaves of sets,
the identification of the inverse image along base change of charts with restriction, and an
identification of functors which collapses three successive restrictions of scalars into one.
The first two are the given comparison on underlying sheaves of sets; the third is *not*
definitional, since it rests on the identity of the two structure maps
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`.  On underlying sheaves of sets,
however, the scalars are forgotten and the two functors of that identification agree on the
nose, so its `CategoryTheory.eqToHom` becomes an identity; that is the content of the private
steps below.

The sheaf of rings is passed explicitly to `CategoryTheory.Sheaf.moduleSheafFunctor` at every
application, as the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleSheafForkReflection.lean` prescribe: with it
left to be inferred, the two `CategoryTheory.GrothendieckTopology.HasSheafCompose` instances are
searched for while the universe of the sections is still a metavariable, and the search does not
reach the instances of the small étale site.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.RingedToposModules

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange
attribute [local instance]
  AlgebraicGeometry.Space.preservesFiniteProducts_smallBaseChange_sheafPushforwardContinuous

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})

omit [J.HasSheafCompose (forget RingCat)] in
/-- **The identification of the inverse image of modules along a restriction functor with
restriction is the identity on underlying sheaves of sets.**  Both sides have the sections of the
module over `G X` as their sections over `X`, and
`Stacks.Sheaves.ToposPullback.restrictionModuleIso` only reads the transported module structure
as the original one. -/
lemma moduleSheafFunctor_map_restrictionModuleIso_hom_app (F : SheafOfModules.{ww} O) :
    (Sheaf.moduleSheafFunctor
          (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O)).map
        ((restrictionModuleIso J K G O).hom.app F) = 𝟙 _ :=
  rfl

/-- **The transport of the inverse image of modules along a natural transformation to the
restriction functor of a continuous functor of sites, followed by the identification of that
inverse image with restriction, is the transformation itself on underlying sheaves of sets.**
The second factor is the identity there, by
`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_restrictionModuleIso_hom_app`, and the
first is `e`, by
`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMapOfNatTrans`.

The two steps are composed here, at a general continuous functor of sites, rather than at the
sheaves they are applied to.  Every conversion between them is a definitional identity of
objects, and on the small étale site of an algebraic space one of those identities has to
reconcile the two spellings of the topology — `AlgebraicGeometry.Space.SmallEtale.topology`,
and the topology of the ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite`, which is
where `AlgebraicGeometry.Space.Modules` reads it from.  That reconciliation unfolds a plain
`def`, so neither `simp` nor `rw` can carry it out, and carrying it out by `exact` on the
sheaves of an algebraic space costs an order of magnitude more than on these variables. -/
lemma moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp
    {Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ]
    (e : Φ ⟶ G.sheafPushforwardContinuous (Type ww) J K)
    (β : pullbackRingSheaf J Φ O ⟶
      pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = e.app (Sheaf.ringSheaf O))
    (F : SheafOfModules.{ww} O) :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
        (pullbackModuleMapOfNatTrans J O e β hβ F ≫
          (SheafOfModules.restrictScalars β).map ((restrictionModuleIso J K G O).hom.app F)) =
      e.app (Sheaf.moduleSheaf O F) := by
  refine (Functor.map_comp _ _ _).trans ?_
  refine (congrArg (CategoryStruct.comp _)
    ((moduleSheafFunctor_map_restrictScalars_map β _).trans
      (moduleSheafFunctor_map_restrictionModuleIso_hom_app J K G O F))).trans ?_
  refine (Category.comp_id _).trans ?_
  exact moduleSheafFunctor_map_pullbackModuleMapOfNatTrans J O e β hβ F

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The sheaf of sets underlying the direct image of an `𝒪_X`-module along base change of étale
scheme charts is the restriction, along that base change, of the sheaf of sets underlying the
module: over an étale chart `V` of `Y` both are the sections of the module over `V ×_Y X`. -/
theorem moduleSheaf_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)
        ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj M) =
      ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M) :=
  rfl

/-- The three steps out of which `AlgebraicGeometry.Space.modulePushforwardChartIso` is built,
written out at a module: the transport along the comparison of the direct images of sheaves of
sets, the identification of the inverse image along base change of charts with restriction, and
the collapse of the three restrictions of scalars into one. -/
private theorem modulePushforwardChartIso_hom_app_eq (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardChartIso B S hS f hf).hom.app M =
      (SheafOfModules.restrictScalars (structureSharp B S hS f)).map
          (pullbackModuleMapOfNatTrans (SmallEtale.topology B S hS Y.1)
              (structureRingSheaf B S hS X)
              (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom
              (chartRingSheafMap B S hS f hf)
              (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
                (structureRingSheaf B S hS X)
                (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom) M ≫
            (SheafOfModules.restrictScalars (chartRingSheafMap B S hS f hf)).map
              ((restrictionModuleIso (SmallEtale.topology B S hS Y.1)
                  (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
                  (structureRingSheaf B S hS X)).hom.app M)) ≫
        (eqToHom (smallBaseChangeModulePushforward_eq B S hS f hf)).app M :=
  rfl

set_option maxHeartbeats 800000 in
/-- The identification of functors which collapses the three restrictions of scalars is the
identity on underlying sheaves of sets: the scalars being forgotten, the two functors agree on
the nose, so the `CategoryTheory.eqToHom` it induces is an identity. -/
private theorem moduleSheafFunctor_map_eqToHom_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
        ((eqToHom (smallBaseChangeModulePushforward_eq B S hS f hf)).app M) = 𝟙 _ :=
  ((congrArg (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
      (eqToHom_app (smallBaseChangeModulePushforward_eq B S hS f hf) M)).trans
    (eqToHom_map _ _)).trans rfl

/-- The first two of the three steps out of which
`AlgebraicGeometry.Space.modulePushforwardChartIso` is built, on underlying sheaves of sets:
the transport of the inverse image of modules along the comparison of the direct images of
sheaves of sets, followed by the identification of the inverse image along base change of charts
with restriction, is that comparison itself.

This is
`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp`
read at the small étale site of `f`.  It is a declaration of its own so that the identification
of `AlgebraicGeometry.Space.structureRingSheafDirectImage` with the inverse-image sheaf of rings
it abbreviates, and that of the two spellings of the small étale topology, are carried out under
their own heartbeat budget rather than under the one that the conversions of
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardChartIso_hom_app` have already
spent. -/
private theorem moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp_chart (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheafDirectImage B S hS f)).map
        (pullbackModuleMapOfNatTrans (SmallEtale.topology B S hS Y.1)
            (structureRingSheaf B S hS X)
            (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom
            (chartRingSheafMap B S hS f hf)
            (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
              (structureRingSheaf B S hS X)
              (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom) M ≫
          (SheafOfModules.restrictScalars (chartRingSheafMap B S hS f hf)).map
            ((restrictionModuleIso (SmallEtale.topology B S hS Y.1)
                (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)
                (structureRingSheaf B S hS X)).hom.app M)) =
      (chartComparison B S hS f hf).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M) :=
  moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (smallBaseChange B S hS f hf) (structureRingSheaf B S hS X)
    (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom
    (chartRingSheafMap B S hS f hf) _ M

/-- **The comparison of the two direct images of `𝒪_X`-modules along a representable morphism is
the comparison of the direct images of sheaves of sets.**  On underlying sheaves of sets
`AlgebraicGeometry.Space.modulePushforwardChartIso` is
`AlgebraicGeometry.Space.chartComparison`: the direct image of modules of Stacks 03LU and the
direct image along base change of étale scheme charts have the same sections, and the comparison
only carries the module structure across them. -/
theorem moduleSheafFunctor_map_modulePushforwardChartIso_hom_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
        ((modulePushforwardChartIso B S hS f hf).hom.app M) =
      (chartComparison B S hS f hf).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M) := by
  refine (congrArg (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)).map
    (modulePushforwardChartIso_hom_app_eq B S hS f hf M)).trans ?_
  refine (Functor.map_comp
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Y)) _
    ((eqToHom (smallBaseChangeModulePushforward_eq B S hS f hf)).app M)).trans ?_
  simp only [moduleSheafFunctor_map_eqToHom_smallBaseChangeModulePushforward]
  exact moduleSheafFunctor_map_pullbackModuleMapOfNatTrans_comp_chart B S hS f hf M

/-- **The comparison of the two direct images of `𝒪_X`-modules, on sections over an étale scheme
chart `V` of `Y`.**  The sections over `V` of the direct image of Stacks 03LU are the limit of
the sections of the module over the étale scheme charts of `X` above the algebraic space
`X ×_Y V`, and the comparison is the projection of that limit to its initial index, the
base-changed chart `V ×_Y X`. -/
theorem modulePushforwardChartIso_hom_app_val_app_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (m : ((modulePushforward B S hS f).obj M).val.obj (op V)) :
    (((modulePushforwardChartIso B S hS f hf).hom.app M).val.app (op V)).hom m =
      chartRanApp B S hS f hf
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M).obj V
        (((smallEtaleDirectImageRanIso B S hS f).hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app
          (op V) m) :=
  congrArg (fun t => t.hom.app (op V) m)
    (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS f hf M)

end AlgebraicGeometry.Space

end
