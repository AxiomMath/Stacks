module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The structure projection of an arbitrary morphism, read through base change of charts

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  `AlgebraicGeometry.Space.modulePushforwardChartIso` identifies the direct
image of modules of Stacks 03LU along `f` with the concrete direct image taken along base change
of étale scheme charts.  This file reads the canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of modules
through that identification: it becomes the morphism of modules attached by
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` to the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp` of the morphism of small étale ringed *sites*.

That canonical morphism is written here for an arbitrary morphism of algebraic spaces.
`AlgebraicGeometry.Space.structureProjection` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean` is its value at the
inclusion of a closed subspace, on the nose.

## Main definitions

* `Stacks.Sheaves.ToposPullback.unitToPullbackModuleObjUnit`: the morphism of modules
  `𝒪 ⟶ Φ_*𝒪'` attached to a comparison `𝒪 ⟶ Φ_*𝒪'` of sheaves of rings, for the inverse image
  of modules along a finite-product-preserving functor of sheaves of sets.
* `AlgebraicGeometry.Space.structureProjectionOfHom`: the canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of
  `𝒪_Y`-modules attached to an arbitrary morphism `f` of algebraic spaces, given on sections by
  the structure map `f♯` of Stacks 03G8.

## Main results

* `Stacks.Sheaves.ToposPullback.unitToPullbackModuleObjUnit_comp_chartIso`: the abstract form of
  the comparison — the composite isomorphism built from
  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`,
  `Stacks.Sheaves.ToposPullback.restrictionModuleIso` and an equality of functors carries the
  morphism of modules attached to a comparison of sheaves of rings to the morphism attached to
  the composite comparison.
* `AlgebraicGeometry.Space.structureProjection_eq_structureProjectionOfHom`: the structure
  projection of a closed subspace is the general morphism at the inclusion.
* `AlgebraicGeometry.Space.structureProjectionOfHom_comp_modulePushforwardChartIso`: **the chart
  layer** — `AlgebraicGeometry.Space.modulePushforwardChartIso` carries `𝒪_Y ⟶ f_*𝒪_X` to the
  morphism of modules attached to `AlgebraicGeometry.Space.smallBaseChangeSharp`.

## Implementation notes

The comparison is proved in the abstract setting of
`Stacks.Sheaves.ToposPullback` and then instantiated.  This is forced, and for the reason
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean`: the equality of
functors `AlgebraicGeometry.Space.smallBaseChangeModulePushforward_eq`, which the final
`CategoryTheory.eqToIso` of `modulePushforwardChartIso` is taken over, holds by three
applications of `CategoryTheory.SheafOfModules.pushforward_comp_restrictScalars` and
`CategoryTheory.Category.comp_id`, each of which is a definitional identity in the abstract
setting but sends the unifier into a `whnf` timeout when the concrete functors are spelled out.
Abstractly the equality is therefore available to proof irrelevance — the proof of it is a
hypothesis of `unitToPullbackModuleObjUnit_comp_chartIso` and is never inspected — so after
substituting the equation of comparisons the whole statement is a definitional identity.  The
concrete statement is then an instantiation and needs no rewriting at all.

Both `unitToPullbackModuleObjUnit` and
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` have the structure map as their own map
on sections, with only `𝒪`-linearity to check, which is multiplicativity of the structure map;
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  {Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww}) {R : Sheaf J RingCat.{ww}}

/-- The morphism of modules `𝒪 ⟶ Φ_*𝒪'` attached to a comparison `a : 𝒪 ⟶ Φ_*𝒪'` of sheaves of
rings, for the inverse image of sheaves of modules along a finite-product-preserving functor `Φ`
of sheaves of sets read as `𝒪`-modules by restriction of scalars along `a`.

Over an object of the site it is the component of `a` with its ring structure forgotten;
`𝒪`-linearity is multiplicativity of that component.  This is
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` for the inverse image along `Φ` instead
of for a continuous functor of sites. -/
noncomputable def unitToPullbackModuleObjUnit (a : R ⟶ pullbackRingSheaf J Φ O) :
    SheafOfModules.unit R ⟶
      (pullbackModuleFunctor J Φ O ⋙ SheafOfModules.restrictScalars a).obj
        (SheafOfModules.unit O) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map (a.hom.app U)) (fun r ↦ by
      ext m
      exact ((a.hom.app U).hom.map_mul r m).symm)
  val.naturality g := by
    ext
    exact ConcreteCategory.congr_hom (a.hom.naturality g) _

variable (Gf : C ⥤ D) [Gf.IsContinuous J K]

/-- **The comparison of the inverse image of modules along `Φ` with restriction along a
continuous functor of sites carries unit morphism to unit morphism.**  Let `ε : Φ ≅ G_*` be a
natural isomorphism of a finite-product-preserving functor of sheaves of sets with restriction
along a continuous functor `G` of sites, let `a : 𝒪 ⟶ Φ_*𝒪'` be a comparison of sheaves of
rings and let `ψ` be the composite comparison `𝒪 ⟶ G_*𝒪'`.  Then the composite isomorphism of
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`,
`Stacks.Sheaves.ToposPullback.restrictionModuleIso` and the identification of the resulting
functor with `CategoryTheory.SheafOfModules.pushforward ψ` carries
`Stacks.Sheaves.ToposPullback.unitToPullbackModuleObjUnit` of `a` to
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` of `ψ`.

The identification of functors is a hypothesis and is never inspected, so the statement is a
definitional identity once the equation of comparisons has been substituted; see the
implementation notes. -/
theorem unitToPullbackModuleObjUnit_comp_chartIso
    (ε : Φ ≅ Gf.sheafPushforwardContinuous (Type ww) J K)
    (a : R ⟶ pullbackRingSheaf J Φ O)
    (ψ : R ⟶ (Gf.sheafPushforwardContinuous RingCat.{ww} J K).obj O)
    (hψ : a ≫ pullbackRingSheafMapOfNatTrans J O ε.hom ≫
      (restrictionRingIso J K Gf O).hom = ψ)
    (hF : ((restrictionModules J K Gf O ⋙
            SheafOfModules.restrictScalars (restrictionRingIso J K Gf O).hom) ⋙
          SheafOfModules.restrictScalars (pullbackRingSheafMapOfNatTrans J O ε.hom)) ⋙
        SheafOfModules.restrictScalars a =
      SheafOfModules.pushforward.{ww} ψ) :
    unitToPullbackModuleObjUnit J K O a ≫
        (Functor.isoWhiskerRight
            (pullbackModuleFunctorIsoOfNatIso J O ε
                (pullbackRingSheafMapOfNatTrans J O ε.hom)
                (ringSheafMap_pullbackRingSheafMapOfNatTrans J O ε.hom) ≪≫
              Functor.isoWhiskerRight (restrictionModuleIso J K Gf O)
                (SheafOfModules.restrictScalars
                  (pullbackRingSheafMapOfNatTrans J O ε.hom)))
            (SheafOfModules.restrictScalars a) ≪≫
          eqToIso hF).hom.app (SheafOfModules.unit O) =
      SheafOfModules.unitToPushforwardObjUnit ψ := by
  subst hψ
  rfl

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

open Stacks.Sheaves.ToposPullback in
/-- **The canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules**, for an arbitrary morphism
`f : X ⟶ Y` of algebraic spaces over `S`: over an object of the small étale site of `Y` it is
the structure map `f♯` of Stacks 03G8, with its ring structure forgotten.

`AlgebraicGeometry.Space.structureProjection` is its value at the inclusion of a closed
subspace. -/
noncomputable def structureProjectionOfHom (f : X ⟶ Y) :
    SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶
      (modulePushforward B S hS f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  unitToPullbackModuleObjUnit (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS X) (structureSharp B S hS f)

/-- The structure projection `𝒪_X ⟶ i_*𝒪_Z` of a closed subspace is the canonical morphism of
modules of the inclusion. -/
theorem structureProjection_eq_structureProjectionOfHom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    structureProjection B S hS X Z =
      structureProjectionOfHom B S hS (subspaceInclusion B S hS X Z) :=
  rfl

open Stacks.Sheaves.ToposPullback in
/-- **The direct image of modules along base change of étale scheme charts carries
`𝒪_Y ⟶ f_*𝒪_X` to the morphism of modules attached to
`AlgebraicGeometry.Space.smallBaseChangeSharp`.**

This is `AlgebraicGeometry.Space.modulePushforwardChartIso` read at the structure sheaf of `X`
as a module over itself: the canonical morphism `𝒪_Y ⟶ f_*𝒪_X` of Stacks 03LU, whose sections
are the structure map of Stacks 03G8, becomes the morphism of modules attached to the structure
map of the morphism of small étale ringed *sites* of a representable morphism.  Its ring-level
content is `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`. -/
theorem structureProjectionOfHom_comp_modulePushforwardChartIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    structureProjectionOfHom B S hS f ≫
        (modulePushforwardChartIso B S hS f hf).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      SheafOfModules.unitToPushforwardObjUnit (smallBaseChangeSharp B S hS f hf) :=
  unitToPullbackModuleObjUnit_comp_chartIso (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS X)
    (smallBaseChange B S hS f hf)
    (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf)
    (structureSharp B S hS f) (smallBaseChangeSharp B S hS f hf)
    (structureSharp_comp_chartRanIso B S hS f hf)
    (smallBaseChangeModulePushforward_eq B S hS f hf)

end AlgebraicGeometry.Space

end
