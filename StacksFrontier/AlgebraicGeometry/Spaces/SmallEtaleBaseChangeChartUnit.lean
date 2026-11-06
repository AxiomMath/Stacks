module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunctionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# The chart projection of the unit of étale restriction of modules

Let `f : X ⟶ Y` be an étale *representable* morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`.  Restriction of modules along `f` has two right adjoints in
this development — the direct image `AlgebraicGeometry.Space.modulePushforward` of Stacks 03LU,
read through the identification of Stacks 03LW, and restriction of sections along base change of
étale scheme charts, `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` — and therefore
two comparisons of them: the adjoint-canonical
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`, which is
`CategoryTheory.Adjunction.rightAdjointUniq`, and the hand-built
`AlgebraicGeometry.Space.modulePushforwardChartIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean`, which is built
through the right Kan extension form of the direct image of sheaves of sets and so mentions
neither adjunction.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeAdjunctionComp.lean` record that
**(†)**, the statement that those two comparisons agree, is the one new input the repaired route
to Stacks 03LY needs, and that it is not of the same kind as the three coherences that route had
already been found circular in: it is a statement at a *single* morphism, and both of the things
it compares have a description on sections.  This file carries out the part of (†) that is about
sections, and reduces (†) itself to one equation of units.  **(†) is not proved here**; see
"What is not done".

## Main definitions

* `AlgebraicGeometry.Space.chartSetProj` and `AlgebraicGeometry.Space.chartModProj` are the chart
  projection of a section of the direct image — of sheaves of sets and of modules respectively:
  the section's value at the base-changed chart `V ×_Y X`, read through the right Kan extension
  form of the direct image.
* `AlgebraicGeometry.Space.chartModuleTransportIso`,
  `AlgebraicGeometry.Space.chartModuleRestrictionIso`,
  `AlgebraicGeometry.Space.chartModuleInnerIso` and
  `AlgebraicGeometry.Space.chartModuleOuterIso` name the four factors of
  `AlgebraicGeometry.Space.modulePushforwardChartIso`, so that each can be evaluated on sections
  separately; `AlgebraicGeometry.Space.modulePushforwardChartIso_eq` is the resulting
  decomposition, which holds by `rfl`.

## Main results

* `AlgebraicGeometry.Space.chartRanApp_ranIso_unit` and its packaged form
  `AlgebraicGeometry.Space.chartSetProj_setRestrictionAdjunction_unit`: **(†) at the level of
  sheaves of sets.**  The unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` — étale restriction of sheaves of
  sets against the direct image, at the universe of the structure rings — projected to the
  base-changed chart `V ×_Y X`, is restriction of sections along the cartesian projection
  `V ×_Y X ⟶ V`.  This is the geometric content of (†), and it is the counterpart at an
  arbitrary sheaf of `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`, which is the
  same statement at the structure sheaf.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app`: **the hand-built
  comparison of the two direct images of modules is, on sections, the chart projection.**  So
  the hand-built comparison is computable on sections, which is what (†) needs of it.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso_eq_chartIso_symm_of_unit`:
  **the reduction of (†) to one equation of units** — (†) holds as soon as the unit of the
  base-change adjunction, followed by the hand-built comparison, is the unit of the adjunction of
  Stacks 03LU read through Stacks 03LW.
* `AlgebraicGeometry.Space.smallEtaleDirectImage_map_inverseImageIso_adj_unit`: the unit of the
  topos-level adjunction of Stacks 03D3, read through the comparison of Stacks 03LQ, is the unit
  of étale restriction of sheaves of sets.  This is
  `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` at
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`, and it is what carries the
  set-level result above to the unit the module-level computation produces.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit`: the
  extension-of-scalars unit followed by the identification of Stacks 03LW is the comparison of
  Stacks 03LQ, on sections.
* `AlgebraicGeometry.Space.chartRanApp_ranIso_naturality`,
  `AlgebraicGeometry.Space.chartSetProj_naturality`,
  `AlgebraicGeometry.Space.chartModProj_map` and
  `AlgebraicGeometry.Space.chartModProj'_map`: the chart projection is natural in the sheaf, so a
  morphism applied before the projection may be applied after it, at the chart.  These are what
  move the two module comparisons of the unit of Stacks 03LU out to the chart, where the two
  previous results compute them.

## Implementation notes

**The Kan-extension bridge.**  `AlgebraicGeometry.Space.chartRanApp` is a projection of the
right Kan extension form of the direct image, whereas the unit of the set-level adjunction is
stated through the quasi-inverse of the comparison equivalence of Stacks 03G1.
`AlgebraicGeometry.Space.ranChartCone_π_ranIso_hom` identifies the two: the projection of the Kan
extension, read through `AlgebraicGeometry.Space.smallEtaleComparisonRanIso`, is the counit of
the comparison equivalence after restriction along the index morphism.  It is
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit` together with naturality, and it is
what lets `AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` — which computes
the unit at *every* index — be read at the initial index.

**The initial index and the counit of the adjunction of sites.**  At the base-changed chart the
morphism of charts that
`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` produces from fullness of
the comparison functor is the counit of
`AlgebraicGeometry.Space.smallEtalePostcompBaseChangeAdjunction`, by
`AlgebraicGeometry.Space.eq_postcompBaseChangeCounit`: both have the cartesian projection as
their underlying morphism, and a morphism of charts out of a postcomposed chart is determined by
that (`AlgebraicGeometry.Space.postcompLeft_injective`).  This is what makes the set-level
result match the unit of the base-change adjunction, which is restriction along that same counit
by `rfl`.

**Elaboration: one declaration per definitional identity.**  Every step below is either a
`rfl` between two spellings of a map of sections or an application of one named lemma, and each
is a *separate* declaration.  That is not cosmetic: the heartbeat budget is per declaration, and
several of these identities cost a large fraction of one.  Two spellings in particular are only
definitionally equal and expensive to reconcile — the sections of
`AlgebraicGeometry.Space.modulePushforward` against those of the four-fold composite that
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward_eq` identifies with base change, and
the ring sheaf of `AlgebraicGeometry.Space.Modules` against
`Stacks.Sheaves.RingedToposModules.structureRingSheaf` — so a proof that reconciles them twice
in one declaration does not elaborate.  The transport along
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward_eq` is handled by
`Stacks.ChartUnit.trans_eqToIso_hom_app_val_app`, which takes the equality of functors as a
hypothesis on *variables* and substitutes it away, so that the `CategoryTheory.eqToIso` never
has to be unfolded at the concrete functors.

**Why the chart projection is defined twice.**  `AlgebraicGeometry.Space.chartModProj` and
`AlgebraicGeometry.Space.chartModProj'` are the same construction as
`AlgebraicGeometry.Space.chartSetProj`, with the section typed through the direct image of
*modules* rather than of the underlying sheaf of sets.  The two are interchangeable by `rfl`, but
only one of them is syntactically compatible with each library lemma, and inserting the
conversion is what the notes above say does not elaborate inside another step.

## Where (†) is finished

**(†) is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeChartUnitTransport.lean`**, as
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso_eq_chartIso_symm`.  What that file
adds is a single sectionwise identity — that the chart projection of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at a module `M` over an étale chart `V`
of `Y` is the restriction of a section along the cartesian projection — together with the
assembly.  Every ingredient of that identity is proved here or in the library:

* the unit of Stacks 03LU is, on sections, the topos-level unit followed by the
  extension-of-scalars unit and the identification of Stacks 03LW — the first step by
  `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`, the decomposition of the
  composite adjunction by `rfl`, and the topos-level step by
  `moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app` in
  `Stacks.Sheaves.RingedToposModules`;
* the two module comparisons move out to the chart by the naturality results above;
* at the chart they are the comparison of Stacks 03LQ, by
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit`;
* that comparison turns the topos-level unit into the set-level unit, by
  `AlgebraicGeometry.Space.smallEtaleDirectImage_map_inverseImageIso_adj_unit`;
* and the set-level unit projects to the restriction along the cartesian projection, by
  `AlgebraicGeometry.Space.chartSetProj_setRestrictionAdjunction_unit`.

What makes the assembly delicate is elaboration, not mathematics, and the two things it needs
are recorded in the implementation notes of that file: the transport of
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app` *under* the chart projection
must be taken with `AlgebraicGeometry.Space.chartSetProj` rather than with
`AlgebraicGeometry.Space.chartModProj`, because the module-level projection makes the elaborator
compare two presheaves of modules whose sections at the pullback of a module are a sheafified
tensor product; and the imported sectionwise identity has to be restated in the consuming file
before it is used.

**No `@[stacks]` attribute is carried.**  Nothing here is an assertion of a numbered result: the
set-level statement is the reading on sections of the unit of Stacks 03LP and 03LQ, whose tags
sit on `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` and its siblings, and the
rest are readings on sections of comparisons that already carry their tags.  In particular
Stacks 03LY and Stacks 03LZ are **not** registered here.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.RingedToposModules

namespace Stacks.ChartUnit

universe w vv uu

variable {CC : Type uu} [Category.{vv} CC] {J : GrothendieckTopology CC}

/-- A composite of morphisms of sheaves of sets acts on sections as the composite of the two
actions. -/
theorem sheafSet_comp_hom_app_apply {A A' A'' : Sheaf J (Type w)} (a : A ⟶ A') (b : A' ⟶ A'')
    (U : CCᵒᵖ) (y : A.obj.obj U) : (a ≫ b).hom.app U y = b.hom.app U (a.hom.app U y) := rfl

variable {R : Sheaf J RingCat.{w}}

/-- On sections, a composite of natural isomorphisms of functors to sheaves of sets acts as the
composite of the two actions. -/
theorem isoTrans_hom_app_hom_app_apply {DD : Type*} [Category DD]
    {F G H : DD ⥤ Sheaf J (Type w)} (al : F ≅ G) (be : G ≅ H) (N : DD) (U : CCᵒᵖ)
    (z : (F.obj N).obj.obj U) :
    ((al ≪≫ be).hom.app N).hom.app U z =
      (be.hom.app N).hom.app U ((al.hom.app N).hom.app U z) := rfl

/-- On sections, the composite of a natural isomorphism with the transport along an equality of
functors to sheaves of modules sends `z` to any section heterogeneously equal to the image of `z`
under the isomorphism. -/
theorem trans_eqToIso_hom_app_val_app {DD : Type*} [Category DD]
    {F G H : DD ⥤ SheafOfModules.{w} R} (al : F ≅ G) (E : G = H) (N : DD) (U : CCᵒᵖ)
    (z : (F.obj N).val.obj U) (t : (H.obj N).val.obj U)
    (ht : HEq ((al.hom.app N).val.app U z) t) :
    ((al ≪≫ eqToIso E).hom.app N).val.app U z = t := by
  subst E
  exact eq_of_heq ht

/-- Whiskering a natural isomorphism of functors to sheaves of modules by restriction of scalars
does not change its action on sections. -/
theorem isoWhiskerRight_restrictScalars_hom_app_val_app {R' : Sheaf J RingCat.{w}} {DD : Type*}
    [Category DD] {F G : DD ⥤ SheafOfModules.{w} R} (Th : F ≅ G) (rho : R' ⟶ R) (N : DD)
    (U : CCᵒᵖ) (z : ((F ⋙ SheafOfModules.restrictScalars rho).obj N).val.obj U) :
    ((Functor.isoWhiskerRight Th (SheafOfModules.restrictScalars rho)).hom.app N).val.app U z =
      (Th.hom.app N).val.app U z := rfl

end Stacks.ChartUnit

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange
attribute [local instance]
  AlgebraicGeometry.Space.preservesFiniteProducts_smallBaseChange_sheafPushforwardContinuous

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The Kan-extension bridge -/

/-- The counit of `comparisonAdjunction` at a sheaf is the counit of the right Kan extension
along the opposite of `comparisonFunctor` at the underlying presheaf. -/
theorem comparisonAdjunction_counit_app_hom (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((comparisonAdjunction B S hS X).counit.app F).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app F.obj := by
  rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]

/-- Restriction of `smallEtaleComparisonRanIso` followed by the counit of `comparisonAdjunction`
is the counit of the comparison equivalence `smallEtaleComparisonRestriction`. -/
theorem restriction_map_ranIso_hom_comp_comparisonCounit (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS X).map
          ((smallEtaleComparisonRanIso B S hS X).hom.app F) ≫
        (comparisonAdjunction B S hS X).counit.app F =
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app F :=
  Adjunction.rightAdjointUniq_hom_app_counit
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
    (comparisonAdjunction B S hS X) F

variable {X Y : AlgebraicSpaces B S hS}

/-- The projection of the right Kan extension at an index `j`, read through
`smallEtaleComparisonRanIso`, is the counit of the comparison equivalence applied after
restriction along the index morphism of `j`. -/
theorem ranChartCone_π_ranIso_hom (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SpacesEtale B S hS X)
    (j : StructuredArrow (op W) (comparisonFunctor B S hS X).op)
    (a : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.obj
      (op W)) :
    (ranChartCone B S hS X F.obj W).π.app j
        (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app (op W) a) =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app F).hom.app
        j.right
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map
          j.hom a) := by
  have hnat := NatTrans.naturality_apply
    ((smallEtaleComparisonRanIso B S hS X).hom.app F).hom j.hom a
  have hc := congrArg
    (fun m : (smallEtaleComparisonRestriction B S hS X).obj
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F) ⟶ F ↦
      m.hom.app j.right
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map
          j.hom a))
    (restriction_map_ranIso_hom_comp_comparisonCounit B S hS X F)
  refine Eq.trans (ranChartCone_π_apply B S hS X F.obj W j _) ?_
  refine Eq.trans (congrArg
    (fun y ↦ ((comparisonFunctor B S hS X).op.ranCounit.app F.obj).app j.right y)
    hnat.symm) ?_
  refine Eq.trans ?_ hc
  exact congrArg
    (fun m ↦ m.app j.right
      (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app
        ((comparisonFunctor B S hS X).op.obj j.right)
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.map
          j.hom a)))
    (comparisonAdjunction_counit_app_hom B S hS X F).symm

/-- The chart projection of the direct image is natural in the sheaf. -/
theorem chartRanApp_ranIso_naturality (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    {F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (al : F ⟶ F')
    (V : SmallEtale B S hS Y.1)
    (y : ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj F).obj.obj
      (op (chartBaseChange B S hS f V))) :
    chartRanApp B S hS f hrep F'.obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app F').hom.app
          (op (chartBaseChange B S hS f V))
          (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map al).hom.app
            (op (chartBaseChange B S hS f V)) y)) =
      al.hom.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartRanApp B S hS f hrep F.obj V
          (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app
            (op (chartBaseChange B S hS f V)) y)) := by
  have hnat : ((smallEtaleComparisonRan B S hS X).map al).hom.app
        (op (chartBaseChange B S hS f V))
        (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app
          (op (chartBaseChange B S hS f V)) y) =
      ((smallEtaleComparisonRanIso B S hS X).hom.app F').hom.app
        (op (chartBaseChange B S hS f V))
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map al).hom.app
          (op (chartBaseChange B S hS f V)) y) :=
    (Stacks.ChartUnit.sheafSet_comp_hom_app_apply
        ((smallEtaleComparisonRanIso B S hS X).hom.app F)
        ((smallEtaleComparisonRan B S hS X).map al)
        (op (chartBaseChange B S hS f V)) y).symm.trans
      ((Sheaf.hom_congr_app_apply ((smallEtaleComparisonRanIso B S hS X).hom.naturality al)
          (op (chartBaseChange B S hS f V)) y).symm.trans
        (Stacks.ChartUnit.sheafSet_comp_hom_app_apply
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map al)
          ((smallEtaleComparisonRanIso B S hS X).hom.app F')
          (op (chartBaseChange B S hS f V)) y))
  refine Eq.trans (congrArg (fun z ↦ chartRanApp B S hS f hrep F'.obj V z) hnat.symm) ?_
  exact ranChartCone_π_naturality B S hS X al.hom (chartBaseChange B S hS f V)
    (smallBaseChangeIndex B S hS f hrep V) _

/-! ### The chart morphism at the initial index is the counit of the adjunction of sites -/

/-- A morphism of charts from the postcomposed initial index to `V` whose image under
`comparisonFunctor` is the counit of `spacesEtalePostcompBaseChangeAdjunction` after the index
morphism is the counit of `smallEtalePostcompBaseChangeAdjunction` at `V`. -/
theorem eq_postcompBaseChangeCounit (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (nu : (smallEtalePostcomp B S hS f hf).obj
      (smallBaseChangeIndex B S hS f hrep V).right.unop ⟶ V)
    (hnu : (comparisonFunctor B S hS Y).map nu =
      (spacesEtalePostcomp B S hS f hf).map (smallBaseChangeIndex B S hS f hrep V).hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS f hf).counit.app
          ((comparisonFunctor B S hS Y).obj V)) :
    nu = (smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V :=
  postcompLeft_injective B S hS f hf _ V
    (((toOver_map_eq_chartBaseChangeMap B S hS f hf V
        (smallBaseChangeIndex B S hS f hrep V) nu hnu).trans
      (chartBaseChangeMap_smallBaseChangeIndex B S hS f hrep V)).trans
      (smallEtalePostcompBaseChangeAdjunction_counit_left B S hS f hf hrep V).symm)

/-! ### The set-level statement -/

/-- The unit of `smallEtaleSetRestrictionAdjunction` at a sheaf of sets `P`, projected to the
base-changed chart of `V`, is restriction of sections of `P` along the counit of
`smallEtalePostcompBaseChangeAdjunction` at `V`. -/
theorem chartRanApp_ranIso_unit (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (x : P.obj.obj (op V)) :
    chartRanApp B S hS f hrep ((smallEtaleSetRestriction B S hS f hf).obj P).obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app
            ((smallEtaleSetRestriction B S hS f hf).obj P)).hom.app
          (op (chartBaseChange B S hS f V))
          (((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app P).hom.app (op V) x)) =
      P.obj.map ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).op x := by
  have := comparisonFunctor_full B S hS Y
  obtain ⟨nu, hnu⟩ : ∃ nu : (smallEtalePostcomp B S hS f hf).obj
        (smallBaseChangeIndex B S hS f hrep V).right.unop ⟶ V,
      (comparisonFunctor B S hS Y).map nu =
        (spacesEtalePostcomp B S hS f hf).map (smallBaseChangeIndex B S hS f hrep V).hom.unop ≫
          (spacesEtalePostcompBaseChangeAdjunction B S hS f hf).counit.app
            ((comparisonFunctor B S hS Y).obj V) :=
    ⟨(comparisonFunctor B S hS Y).preimage _, (comparisonFunctor B S hS Y).map_preimage _⟩
  refine Eq.trans (ranChartCone_π_ranIso_hom B S hS X
    ((smallEtaleSetRestriction B S hS f hf).obj P) (chartBaseChange B S hS f V)
    (smallBaseChangeIndex B S hS f hrep V) _) ?_
  refine Eq.trans (counitIso_hom_app_restrictionAdjunction_unit B S hS f hf P V
    (smallBaseChangeIndex B S hS f hrep V) x nu hnu) ?_
  exact congrArg (fun m ↦ P.obj.map (Quiver.Hom.op m) x)
    (eq_postcompBaseChangeCounit B S hS f hf hrep V nu hnu)


open Stacks.Sheaves.ToposPullback in
/-- The isomorphism `restrictionModuleIso` acts as the identity on sections. -/
theorem restrictionModuleIso_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ((pullbackModuleFunctor.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y.1)
        ((smallBaseChange B S hS f hrep).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1))
        (structureRingSheaf B S hS X)).obj N).val.obj V) :
    ((restrictionModuleIso (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
        (smallBaseChange B S hS f hrep) (structureRingSheaf B S hS X)).hom.app N).val.app V z =
      z := rfl

open Stacks.Sheaves.ToposPullback in
/-- On sections, the transport of the module structure along the chart comparison of sheaves of
sets acts as that comparison of the underlying sheaves of sets. -/
theorem pullbackModuleFunctorIsoOfNatIso_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (n : ((modulePushforward B S hS f).obj N).val.obj V) :
    ((pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B S hS Y.1)
          (structureRingSheaf B S hS X)
          (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hrep)
          (chartRingSheafMap B S hS f hrep)
          (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
            (structureRingSheaf B S hS X)
            (smallEtaleDirectImageRanIso B S hS f ≪≫
              chartRanIso B S hS f hrep).hom)).hom.app N).val.app V n =
      ((smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hrep).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app V n := rfl

open Stacks.Sheaves.ToposPullback in
/-- The transport of the module structure along the chart comparison of sheaves of sets. -/
noncomputable def chartModuleTransportIso (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) :=
  pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B S hS Y.1)
    (structureRingSheaf B S hS X)
    (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hrep)
    (chartRingSheafMap B S hS f hrep)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X)
      (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hrep).hom)

open Stacks.Sheaves.ToposPullback in
/-- The identification of the transported inverse image with restriction. -/
noncomputable def chartModuleRestrictionIso (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) :=
  Functor.isoWhiskerRight
    (restrictionModuleIso (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
      (smallBaseChange B S hS f hrep) (structureRingSheaf B S hS X))
    (SheafOfModules.restrictScalars (chartRingSheafMap B S hS f hrep))

/-- The inner comparison of `modulePushforwardChartIso`. -/
noncomputable def chartModuleInnerIso (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) :=
  chartModuleTransportIso B S hS f hrep ≪≫ chartModuleRestrictionIso B S hS f hrep

/-- The comparison of `modulePushforwardChartIso` before the transport of functors. -/
noncomputable def chartModuleOuterIso (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) :=
  Functor.isoWhiskerRight (chartModuleInnerIso B S hS f hrep)
    (SheafOfModules.restrictScalars (structureSharp B S hS f))

/-- `modulePushforwardChartIso` is `chartModuleOuterIso` followed by the transport along
`smallBaseChangeModulePushforward_eq`. -/
theorem modulePushforwardChartIso_eq (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) :
    modulePushforwardChartIso B S hS f hrep =
      chartModuleOuterIso B S hS f hrep ≪≫
        eqToIso (smallBaseChangeModulePushforward_eq B S hS f hrep) := rfl

open Stacks.Sheaves.RingedToposModules in
/-- The inner comparison on sections is the chart projection. -/
theorem chartModuleInnerIso_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((chartModuleInnerIso B S hS f hrep).hom.app N).val.app (op V) n =
      chartRanApp B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
          (op (chartBaseChange B S hS f V)) n) := by
  refine Eq.trans (isoTrans_hom_app_val_app (chartModuleTransportIso B S hS f hrep)
    (chartModuleRestrictionIso B S hS f hrep) N (op V) n) ?_
  refine Eq.trans (Stacks.ChartUnit.isoWhiskerRight_restrictScalars_hom_app_val_app
    (Stacks.Sheaves.ToposPullback.restrictionModuleIso (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hrep)
      (structureRingSheaf B S hS X))
    (chartRingSheafMap B S hS f hrep) N (op V) _) ?_
  refine Eq.trans (restrictionModuleIso_hom_app_val_app B S hS f hrep N (op V) _) ?_
  refine Eq.trans
    (pullbackModuleFunctorIsoOfNatIso_hom_app_val_app B S hS f hrep N (op V) n) ?_
  exact Stacks.ChartUnit.isoTrans_hom_app_hom_app_apply (smallEtaleDirectImageRanIso B S hS f)
    (chartRanIso B S hS f hrep)
    (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N) (op V) n

open Stacks.Sheaves.RingedToposModules in
/-- The outer comparison on sections is the chart projection. -/
theorem chartModuleOuterIso_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((chartModuleOuterIso B S hS f hrep).hom.app N).val.app (op V) n =
      chartRanApp B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
          (op (chartBaseChange B S hS f V)) n) :=
  (Stacks.ChartUnit.isoWhiskerRight_restrictScalars_hom_app_val_app
      (chartModuleInnerIso B S hS f hrep) (structureSharp B S hS f) N (op V) n).trans
    (chartModuleInnerIso_hom_app_val_app B S hS f hrep N V n)

open Stacks.Sheaves.RingedToposModules in
/-- The transport along the equality of the two spellings of the base-change direct image is the
identity on sections. -/
theorem eqToIso_smallBaseChangeModulePushforward_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (w : ((smallBaseChangeModulePushforward.{u, u} B S hS f hrep).obj N).val.obj (op V)) :
    ((eqToIso (smallBaseChangeModulePushforward_eq B S hS f hrep)).hom.app N).val.app (op V) w =
      w :=
  (eqToIso_hom_app_val_app (smallBaseChangeModulePushforward_eq B S hS f hrep) N (op V) w).trans
    rfl

open Stacks.Sheaves.RingedToposModules in
/-- The explicit form of the comparison, on sections. -/
theorem chartIsoExplicit_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((chartModuleOuterIso B S hS f hrep ≪≫
          eqToIso (smallBaseChangeModulePushforward_eq B S hS f hrep)).hom.app N).val.app
        (op V) n =
      chartRanApp B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
          (op (chartBaseChange B S hS f V)) n) :=
  Stacks.ChartUnit.trans_eqToIso_hom_app_val_app (chartModuleOuterIso B S hS f hrep)
    (smallBaseChangeModulePushforward_eq B S hS f hrep) N (op V) n _
    (heq_of_eq (chartModuleOuterIso_hom_app_val_app B S hS f hrep N V n))

open Stacks.Sheaves.RingedToposModules in
/-- **The comparison of the direct images on sections is the chart projection.** -/
theorem modulePushforwardChartIso_hom_app_val_app (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hrep).hom.app N).val.app (op V) n =
      chartRanApp B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V
        (((smallEtaleComparisonRanIso B S hS X).hom.app
            (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
          (op (chartBaseChange B S hS f V)) n) :=
  (congrArg (fun e : modulePushforward B S hS f ≅
      smallBaseChangeModulePushforward.{u, u} B S hS f hrep ↦ (e.hom.app N).val.app (op V) n)
    (modulePushforwardChartIso_eq B S hS f hrep)).trans
    (chartIsoExplicit_hom_app_val_app B S hS f hrep N V n)

/-- The chart projection of a section of the direct image of sheaves of sets. -/
noncomputable def chartSetProj (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (z : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op V)) :
    F.obj.obj (op ((smallBaseChange B S hS f hrep).obj V)) :=
  chartRanApp B S hS f hrep F.obj V
    (((smallEtaleComparisonRanIso B S hS X).hom.app F).hom.app
      (op (chartBaseChange B S hS f V)) z)

/-- The chart projection is natural in the sheaf of sets. -/
theorem chartSetProj_naturality (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)
    {F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (al : F ⟶ F')
    (V : SmallEtale B S hS Y.1)
    (z : ((smallEtaleDirectImage B S hS f).obj F).obj.obj (op V)) :
    chartSetProj B S hS f hrep F' V (((smallEtaleDirectImage B S hS f).map al).hom.app (op V) z) =
      al.hom.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep F V z) :=
  chartRanApp_ranIso_naturality B S hS f hrep al V z

/-- **The chart projection of the unit of étale restriction of sheaves of sets is restriction
along the cartesian projection.** -/
theorem chartSetProj_setRestrictionAdjunction_unit (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (x : P.obj.obj (op V)) :
    chartSetProj B S hS f hrep ((smallEtaleSetRestriction B S hS f hf).obj P) V
        (((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app P).hom.app (op V) x) =
      P.obj.map ((smallEtalePostcompBaseChangeAdjunction B S hS f hf hrep).counit.app V).op x :=
  chartRanApp_ranIso_unit B S hS f hf hrep P V x

section Unit

variable (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)

open Stacks.Sheaves.RingedToposModules in
/-- The direct image of modules acts on sections as the direct image of sheaves of sets, read at
the base-changed chart. -/
theorem modulePushforward_map_val_app (N N' : Modules.{u, u} B S hS X.1 X.2) (al : N ⟶ N')
    (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((modulePushforward B S hS f).map al).val.app (op V) z =
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map al)).hom.app
        (op (chartBaseChange B S hS f V))) z := rfl

open Stacks.Sheaves.RingedToposModules in
/-- The topos-level direct image of modules acts on sections as the direct image of sheaves of
sets, read at the base-changed chart. -/
theorem directImageModules_map_val_app
    {P P' : SheafOfModules.{u}
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y))}
    (al : P ⟶ P') (V : SmallEtale B S hS Y.1)
    (z : ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj P).val.obj (op V)) :
    (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).map al).val.app (op V)) z =
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.map
          ((Sheaf.moduleSheafFunctor
            (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y))).map al)).hom.app
        (op (chartBaseChange B S hS f V))) z := rfl


open Stacks.Sheaves.RingedToposModules in
/-- The chart projection commutes with the direct image of modules of Stacks 03LU. -/
theorem chartSetProj_modulePushforward_map {N N' : Modules.{u, u} B S hS X.1 X.2} (al : N ⟶ N')
    (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartSetProj B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N') V
        (((modulePushforward B S hS f).map al).val.app (op V) z) =
      al.val.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N) V z) :=
  chartRanApp_ranIso_naturality B S hS f hrep
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map al) V z

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection commutes with the topos-level direct image of modules. -/
theorem chartSetProj_directImageModules_map
    {P P' : SheafOfModules.{u}
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y))}
    (al : P ⟶ P') (V : SmallEtale B S hS Y.1)
    (z : ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj P).val.obj (op V)) :
    chartSetProj B S hS f hrep
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)) P') V
        (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).map al).val.app (op V) z) =
      al.val.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          (Sheaf.moduleSheaf.{u, u, u + 1}
            (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)) P) V z) :=
  chartRanApp_ranIso_naturality B S hS f hrep
    ((Sheaf.moduleSheafFunctor
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y))).map al) V z

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection commutes with the direct image of sheaves of sets of the comparison of
Stacks 03LQ. -/
theorem chartSetProj_smallEtaleDirectImage_map_inverseImageIso
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (z : ((smallEtaleDirectImage B S hS f).obj
      ((smallToposMorphismTypeU B S hS f).inverseImage.obj G)).obj.obj (op V)) :
    chartSetProj B S hS f hrep ((smallEtaleSetRestriction B S hS f hf).obj G) V
        (((smallEtaleDirectImage B S hS f).map
            ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app G)).hom.app
          (op V) z) =
      ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app G).hom.app
        (op ((smallBaseChange B S hS f hrep).obj V))
        (chartSetProj B S hS f hrep
          ((smallToposMorphismTypeU B S hS f).inverseImage.obj G) V z) :=
  chartSetProj_naturality B S hS f hrep
    ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app G) V z

open Stacks.Sheaves.RingedToposModules in
/-- **The unit of the adjunction of Stacks 03LU at the topos level, read through the comparison
of Stacks 03LQ, is the unit of étale restriction of sheaves of sets.** -/
theorem smallEtaleDirectImage_map_inverseImageIso_adj_unit
    (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (x : G.obj.obj (op V)) :
    ((smallEtaleDirectImage B S hS f).map
          ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app G)).hom.app (op V)
        (((smallToposMorphismTypeU B S hS f).adj.unit.app G).hom.app (op V) x) =
      ((smallEtaleSetRestrictionAdjunction B S hS f hf).unit.app G).hom.app (op V) x :=
  Sheaf.hom_congr_app_apply
    (Adjunction.unit_leftAdjointUniq_hom_app (smallToposMorphismTypeU B S hS f).adj
      (smallEtaleSetRestrictionAdjunction B S hS f hf) G) (op V) x

open Stacks.Sheaves.RingedToposModules in
/-- **The extension-of-scalars unit followed by the identification of Stacks 03LW is the
comparison of Stacks 03LQ**, on sections. -/
theorem modulePullbackIsoEtaleModulePullback_hom_app_extendScalars_unit
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj M).val.obj U) :
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M).val.app U
        (((extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj M)).val.app U m) =
      ((smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app U m :=
  modulePullbackIsoEtaleModulePullback_unit_app B S hS f hf M U m

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection of a section of the direct image of modules of Stacks 03LU. -/
noncomputable def chartModProj (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    N.val.obj (op ((smallBaseChange B S hS f hrep).obj V)) :=
  chartRanApp B S hS f hrep
    (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V
    (((smallEtaleComparisonRanIso B S hS X).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
      (op (chartBaseChange B S hS f V)) z)

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection of a section of the topos-level direct image of modules. -/
noncomputable def chartModProj'
    (P : SheafOfModules.{u}
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y)))
    (V : SmallEtale B S hS Y.1)
    (z : ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj P).val.obj (op V)) :
    P.val.obj (op ((smallBaseChange B S hS f hrep).obj V)) :=
  chartRanApp B S hS f hrep
    (Sheaf.moduleSheaf.{u, u, u + 1}
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) P).obj V
    (((smallEtaleComparisonRanIso B S hS X).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)) P)).hom.app
      (op (chartBaseChange B S hS f V)) z)

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection commutes with the direct image of a morphism of modules. -/
theorem chartModProj_map {N N' : Modules.{u, u} B S hS X.1 X.2} (al : N ⟶ N')
    (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hrep N' V (((modulePushforward B S hS f).map al).val.app (op V) z) =
      al.val.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartModProj B S hS f hrep N V z) :=
  chartSetProj_modulePushforward_map B S hS f hrep al V z

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection commutes with the topos-level direct image of a morphism of modules. -/
theorem chartModProj'_map
    {P P' : SheafOfModules.{u}
      (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureRingSheaf B S hS Y))}
    (al : P ⟶ P') (V : SmallEtale B S hS Y.1)
    (z : ((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj P).val.obj (op V)) :
    chartModProj' B S hS f hrep P' V
        (((directImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).map al).val.app (op V) z) =
      al.val.app (op ((smallBaseChange B S hS f hrep).obj V))
        (chartModProj' B S hS f hrep P V z) :=
  chartSetProj_directImageModules_map B S hS f hrep al V z

/-! ### The reduction of (†) to the unit equation -/

/-- **(†) follows from the unit equation.**  If the unit of the base-change adjunction, followed
by the hand-built comparison of the two direct images, is the unit of the adjunction of
Stacks 03LU read through Stacks 03LW, then the adjoint-canonical comparison
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso` *is* that hand-built comparison.

The comparison of two right adjoints is the conjugate of the identity of the shared left
adjoint, and an adjunction whose unit is the unit of another one followed by an isomorphism of
right adjoints is that other one transported along the isomorphism; the conjugate of the
identity between an adjunction and such a transport is the isomorphism itself
(`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_hom`). -/
theorem smallBaseChangeModulePushforwardIso_eq_chartIso_symm_of_unit
    (hu : (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).unit ≫
        Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS f hf)
          (modulePushforwardChartIso B S hS f hrep).inv =
      (etaleModulePullbackAdjunction B S hS f hf).unit) :
    smallBaseChangeModulePushforwardIso B S hS f hf hrep =
      (modulePushforwardChartIso B S hS f hrep).symm := by
  have hb : etaleModulePullbackAdjunction B S hS f hf =
      (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep).ofNatIsoRight
        (modulePushforwardChartIso B S hS f hrep).symm :=
    Adjunction.ext hu.symm
  exact Iso.ext ((congrArg
    (fun adj : etaleModulePullback.{u, u} B S hS f hf ⊣ modulePushforward B S hS f ↦
      (Adjunction.rightAdjointUniq
        (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep) adj).hom) hb).trans
    (Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_hom
      (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep)
      (modulePushforwardChartIso B S hS f hrep).symm))

end Unit


end AlgebraicGeometry.Space

end
