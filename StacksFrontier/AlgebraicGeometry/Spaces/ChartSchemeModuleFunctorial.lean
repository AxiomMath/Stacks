module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections

/-!
# The chart restriction of a quasi-coherent module as a functor

`AlgebraicGeometry.Space.chartSmallEtaleRestriction`, `AlgebraicGeometry.Space.chartSchemeQcoh`
and `AlgebraicGeometry.Space.chartSchemeModule` are all defined *objectwise*: each takes a module
(and, for the last two, a proof of quasi-coherence) and returns a module, with no action on
morphisms.  So there is nothing for
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` to be natural in, and a morphism of
`𝒪_X`-modules — such as the inclusion `ℐⁿ𝒢 ⟶ 𝒢` — cannot be transported to the chart at all.

This file supplies the missing functors and the naturality square.  It is bookkeeping rather than
mathematics: every ingredient is already natural.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeRestrictionFunctor`: restriction to the small étale site
  of a chart, as a functor.
* `AlgebraicGeometry.Space.chartSmallEtaleQcohFunctor`,
  `AlgebraicGeometry.Space.chartSchemeEtaleQcohFunctor`,
  `AlgebraicGeometry.Space.chartSchemeQcohFunctor`: the same on the quasi-coherent modules, and
  its composites with the two equivalences.
* `AlgebraicGeometry.Space.chartSchemeModuleFunctor` and
  `AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor`: the underlying sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.chartSchemeModuleFunctor_obj`,
  `AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor_obj` and the `obj` lemmas beside them:
  the functors agree on objects with the objectwise constructions, by `rfl`.
* `AlgebraicGeometry.Space.chartSchemeQcohFunctor_eq`: the chart restriction functor is the
  restriction to the small étale site of the chart scheme followed by the inverse of the
  equivalence of Descent, Proposition 03DX (2), definitionally.
* `Stacks.CategoryTheory.comp_unit_comp_map`: the abstract square built from the unit of an
  adjunction and a commuting square out of the left adjoint.
* `AlgebraicGeometry.Space.counit_naturality_chartSchemeEtaleQcohFunctor` and
  `AlgebraicGeometry.Space.associatedModuleChartSchemeModuleIso_naturality`: the second factor of
  the chart transport is natural.
* `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` and
  `AlgebraicGeometry.Space.chartSchemeModuleFunctorIsoRestrictModule`: **the chart restriction of
  a quasi-coherent `𝒪_X`-module is naturally isomorphic, as a functor of the module, to the
  restriction along the inclusion of the small Zariski site of its restriction to the small étale
  site of the chart scheme**, with
  `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` as its components.

## Implementation notes

The functors are assembled from `CategoryTheory.SheafOfModules.overFunctor` and
`CategoryTheory.SheafOfModules.pushforward` — `AlgebraicGeometry.Space.chartSmallEtaleRestriction`
is their composite read at one object — then corestricted to the quasi-coherent modules by
`CategoryTheory.ObjectProperty.lift` and composed with the inverses of the two comparison
equivalences.  Every `obj` lemma below is `rfl`: the objectwise definitions were already these
functors applied to an object, and the membership field of a full subcategory is a proposition.

The naturality square has two halves, and both are naturality of something already natural:

* the unit of `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`, which is where
  `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` gets its first factor;
* the counit of `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, which is its second.

What makes them compose is that
`AlgebraicGeometry.Space.chartSchemeQcohFunctor` *is* `chartSchemeEtaleQcohFunctor` followed by
the inverse of that equivalence, `AlgebraicGeometry.Space.chartSchemeQcohFunctor_eq`, and that
the corestriction of the associated-module functor to the quasi-coherent modules is
`CategoryTheory.ObjectProperty.lift`, so that composing it back with the inclusion returns the
uncorestricted functor on the nose.

**The square is glued by an abstract lemma, and that is not a stylistic choice.**  The concrete
naturality goal is large, and on it every rewrite whose pattern is headed by a composition —
`CategoryTheory.Category.assoc`, `CategoryTheory.Adjunction.unit_naturality`,
`CategoryTheory.Functor.map_comp` — spends the entire heartbeat budget inside `isDefEq`, testing
the pattern against each of the many composites and functor applications the goal contains.  The
same rewrites on `Stacks.CategoryTheory.comp_unit_comp_map`, whose goal has four morphisms in it,
are instant, and the concrete statement then follows from it by a single `exact`, whose
definitional check decomposes into the component identifications, each of which is `rfl` on its
own.  For the same reason
`AlgebraicGeometry.Space.associatedModuleChartSchemeModuleIso_naturality` distributes
`CategoryTheory.Functor.map_comp` by `Eq.trans` rather than by `rw ... at`: the rewrite leaves
a subterm whose argument is not a composition, and deciding that costs the budget.

No declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to a
chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- **A square built from the unit of an adjunction and a morphism out of the left adjoint.**
Let `L ⊣ R`, let `a : P ⟶ Q` and let `cP : L.obj P ⟶ Y`, `cQ : L.obj Q ⟶ Y'` and `d : Y ⟶ Y'`
make the evident square commute.  Then the two composites

`P ⟶ Q ⟶ R(L Q) ⟶ R Y'`  and  `P ⟶ R(L P) ⟶ R Y ⟶ R Y'`

agree.

This is the shape of the naturality square of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`, isolated so that the rewrites are
performed on a goal of this size: the concrete goal is large enough that a rewrite whose pattern
is headed by a composition spends the whole heartbeat budget in `isDefEq` on candidate
subterms. -/
theorem comp_unit_comp_map {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {P Q : C} (a : P ⟶ Q) {Y Y' : D} (cP : L.obj P ⟶ Y) (cQ : L.obj Q ⟶ Y')
    (d : Y ⟶ Y') (h : L.map a ≫ cQ = cP ≫ d) :
    a ≫ (adj.unit.app Q ≫ R.map cQ) = (adj.unit.app P ≫ R.map cP) ≫ R.map d := by
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, h]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Restriction to the small étale site of a chart, as a functor -/

/-- **The restriction of an `𝒪_X`-module to an étale chart, read on the small étale site of the
chart, as a functor of the module.**

This is `CategoryTheory.SheafOfModules.overFunctor` followed by the pushforward along the
comparison functor of Stacks 04M0, which is what
`AlgebraicGeometry.Space.chartSmallEtaleRestriction` is at one object. -/
noncomputable def chartSchemeRestrictionFunctor (V : SmallEtale B S hS X.1) :
    SheafOfModules.{u} (structureRingSheaf B S hS X) ⥤
      SheafOfModules.{u} (chartStructureRingSheaf B S hS X V) :=
  SheafOfModules.overFunctor (structureRingSheaf B S hS X) V ⋙
    @SheafOfModules.pushforward _ _ _ _
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V)
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor
      (chartStructureRingSheaf B S hS X V)
      ((structureRingSheaf B S hS X).over V)
      (isContinuous_chartLocalization_chartSpace B S hS X V)
      (𝟙 _)

/-- The chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSmallEtaleRestriction`. -/
theorem chartSchemeRestrictionFunctor_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (V : SmallEtale B S hS X.1) :
    (chartSchemeRestrictionFunctor B S hS X V).obj M
      = chartSmallEtaleRestriction B S hS X M V := rfl

/-- **The restriction of a quasi-coherent `𝒪_X`-module to an étale chart, as a functor of the
module**, with values in the quasi-coherent modules on the small étale site of the chart.

The corestriction is possible by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction`. -/
noncomputable def chartSmallEtaleQcohFunctor (V : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (chartStructureRingSheaf B S hS X V)).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureRingSheaf B S hS X)).ι ⋙
      chartSchemeRestrictionFunctor B S hS X V)
    fun M => isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS X M.obj M.property V

/-- The quasi-coherent chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSmallEtaleQcoh`. -/
theorem chartSmallEtaleQcohFunctor_obj
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) (V : SmallEtale B S hS X.1) :
    (chartSmallEtaleQcohFunctor B S hS X V).obj M
      = chartSmallEtaleQcoh B S hS X M.obj M.property V := rfl

/-! ### The two transports, as functors -/

/-- **The restriction of a quasi-coherent `𝒪_X`-module to the small étale site of an étale scheme
chart, as a functor of the module.**  This is
`AlgebraicGeometry.Space.chartSchemeEtaleQcoh` with its action on morphisms. -/
noncomputable def chartSchemeEtaleQcohFunctor (A : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS
          ((SmallEtale.toOver B S hS X.1).obj A))).FullSubcategory :=
  chartSmallEtaleQcohFunctor B S hS X A ⋙
    (representedQuasicoherentEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj A)).inverse

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module, as a functor of the module**, with
values in the quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the chart scheme.  This is
`AlgebraicGeometry.Space.chartSchemeQcoh` with its action on morphisms. -/
noncomputable def chartSchemeQcohFunctor (A : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).FullSubcategory :=
  chartSmallEtaleQcohFunctor B S hS X A ⋙
    (representedQuasicoherentSchemeEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj A)).inverse

/-- The chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSchemeQcoh`. -/
theorem chartSchemeQcohFunctor_obj
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) (A : SmallEtale B S hS X.1) :
    (chartSchemeQcohFunctor B S hS X A).obj M
      = chartSchemeQcoh B S hS X M.obj M.property A := rfl

/-- The small-étale chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSchemeEtaleQcoh`. -/
theorem chartSchemeEtaleQcohFunctor_obj
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) (A : SmallEtale B S hS X.1) :
    (chartSchemeEtaleQcohFunctor B S hS X A).obj M
      = chartSchemeEtaleQcoh B S hS X M.obj M.property A := rfl

/-- **The chart restriction functor factors through the small étale site of the chart scheme.**
Precisely, it is the restriction to that site followed by the inverse of the equivalence of
Descent, Proposition 03DX (2) for the chart scheme, definitionally.

This is what makes the two halves of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` compose: the counit of the
equivalence is natural in the module on the small étale site, and that module is the value of
`AlgebraicGeometry.Space.chartSchemeEtaleQcohFunctor`. -/
theorem chartSchemeQcohFunctor_eq (A : SmallEtale B S hS X.1) :
    chartSchemeQcohFunctor B S hS X A =
      chartSchemeEtaleQcohFunctor B S hS X A ⋙
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) (chartScheme A)
          ((SmallEtale.toOver B S hS X.1).obj A).left.property).inverse := rfl

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module as an
`AlgebraicGeometry.Scheme.Modules` on the chart scheme, functorially in the module.** -/
noncomputable abbrev chartSchemeModuleFunctor (A : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).FullSubcategory ⥤
      AlgebraicGeometry.Scheme.Modules (chartScheme A) :=
  chartSchemeQcohFunctor B S hS X A ⋙
    (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι

/-- **The restriction of a quasi-coherent `𝒪_X`-module to the small étale site of the chart
scheme, as a sheaf of modules, functorially in the module.** -/
noncomputable abbrev chartSchemeEtaleModuleFunctor (A : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf B S hS X)).FullSubcategory ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) (chartScheme A)
        ((SmallEtale.toOver B S hS X.1).obj A).left.property) :=
  chartSchemeEtaleQcohFunctor B S hS X A ⋙
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι

/-- The chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSchemeModule`. -/
theorem chartSchemeModuleFunctor_obj
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) (A : SmallEtale B S hS X.1) :
    (chartSchemeModuleFunctor B S hS X A).obj M
      = chartSchemeModule B S hS X M.obj M.property A := rfl

/-- The small-étale chart restriction functor agrees on objects with
`AlgebraicGeometry.Space.chartSchemeEtaleModule`. -/
theorem chartSchemeEtaleModuleFunctor_obj
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) (A : SmallEtale B S hS X.1) :
    (chartSchemeEtaleModuleFunctor B S hS X A).obj M
      = chartSchemeEtaleModule B S hS X M.obj M.property A := rfl

/-! ### Naturality of the chart transport -/

/-- The two factors of `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`: the unit of
the associated-module adjunction of the chart scheme, and the restriction along the inclusion of
the small Zariski site of the counit of the equivalence of Descent, Proposition 03DX (2). -/
theorem chartSchemeModuleIsoRestrictModule_hom
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom
      = (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
            (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).unit.app
          (chartSchemeQcoh B S hS X M hM A).obj ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).map
          (associatedModuleChartSchemeModuleIso B S hS X M hM A).hom := rfl

/-- **The counit of the equivalence of Descent, Proposition 03DX (2) is natural in the
`𝒪_X`-module**, read in the category of quasi-coherent modules on the small étale site of the
chart scheme.

This is the naturality of that counit at the morphism which
`AlgebraicGeometry.Space.chartSchemeEtaleQcohFunctor` produces, with the two sides spelled
through the functors of this file. -/
theorem counit_naturality_chartSchemeEtaleQcohFunctor (A : SmallEtale B S hS X.1)
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : M ⟶ N) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) (chartScheme A)
          ((SmallEtale.toOver B S hS X.1).obj A).left.property).functor.map
        ((chartSchemeQcohFunctor B S hS X A).map φ) ≫
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) (chartScheme A)
          ((SmallEtale.toOver B S hS X.1).obj A).left.property).counitIso.hom.app
        (chartSchemeEtaleQcoh B S hS X N.obj N.property A)
    = (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) (chartScheme A)
          ((SmallEtale.toOver B S hS X.1).obj A).left.property).counitIso.hom.app
        (chartSchemeEtaleQcoh B S hS X M.obj M.property A) ≫
      (chartSchemeEtaleQcohFunctor B S hS X A).map φ :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
      (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property).counitIso.hom.naturality
    ((chartSchemeEtaleQcohFunctor B S hS X A).map φ)

/-- **The square identifying the associated module of the chart restriction with the restriction
to the small étale site of the chart scheme is natural in the `𝒪_X`-module.**

This is `AlgebraicGeometry.Space.counit_naturality_chartSchemeEtaleQcohFunctor` pushed forward
along the inclusion of the quasi-coherent modules, which is where the corestriction of the
associated-module functor to the quasi-coherent modules becomes that functor itself. -/
theorem associatedModuleChartSchemeModuleIso_naturality (A : SmallEtale B S hS X.1)
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : M ⟶ N) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).map
        ((chartSchemeModuleFunctor B S hS X A).map φ) ≫
      (associatedModuleChartSchemeModuleIso B S hS X N.obj N.property A).hom
    = (associatedModuleChartSchemeModuleIso B S hS X M.obj M.property A).hom ≫
      (chartSchemeEtaleModuleFunctor B S hS X A).map φ :=
  have h := congrArg (fun k =>
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS
        ((SmallEtale.toOver B S hS X.1).obj A))).ι.map k)
    (counit_naturality_chartSchemeEtaleQcohFunctor B S hS X A φ)
  (((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS
        ((SmallEtale.toOver B S hS X.1).obj A))).ι.map_comp _ _).symm.trans
    (h.trans ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS
        ((SmallEtale.toOver B S hS X.1).obj A))).ι.map_comp _ _)))

/-- **The chart transport is natural in the module**: the naturality square of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` for the functors of this file.

Both halves are naturality of something already natural — the unit of the associated-module
adjunction and the counit of the equivalence of Descent, Proposition 03DX (2) — and
`Stacks.CategoryTheory.comp_unit_comp_map` is what glues them. -/
theorem chartSchemeModuleIsoRestrictModule_naturality (A : SmallEtale B S hS X.1)
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : M ⟶ N) :
    (chartSchemeModuleFunctor B S hS X A).map φ ≫
        (chartSchemeModuleIsoRestrictModule B S hS X N.obj N.property A).hom
      = (chartSchemeModuleIsoRestrictModule B S hS X M.obj M.property A).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property).map
          ((chartSchemeEtaleModuleFunctor B S hS X A).map φ) :=
  Stacks.CategoryTheory.comp_unit_comp_map
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property)
    ((chartSchemeModuleFunctor B S hS X A).map φ)
    (associatedModuleChartSchemeModuleIso B S hS X M.obj M.property A).hom
    (associatedModuleChartSchemeModuleIso B S hS X N.obj N.property A).hom
    ((chartSchemeEtaleModuleFunctor B S hS X A).map φ)
    (associatedModuleChartSchemeModuleIso_naturality B S hS X A φ)

/-- **The chart restriction of a quasi-coherent `𝒪_X`-module is naturally isomorphic, as a
functor of the module, to the restriction along the inclusion of the small Zariski site of its
restriction to the small étale site of the chart scheme.**

This is `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` upgraded to a natural
isomorphism, which is what lets a morphism of quasi-coherent `𝒪_X`-modules — such as the
inclusion of a submodule — be transported to the chart scheme compatibly with the identification
of the chart transport with the restriction functor. -/
noncomputable def chartSchemeModuleFunctorIsoRestrictModule (A : SmallEtale B S hS X.1) :
    chartSchemeModuleFunctor B S hS X A ≅
      chartSchemeEtaleModuleFunctor B S hS X A ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          (chartScheme A) ((SmallEtale.toOver B S hS X.1).obj A).left.property :=
  NatIso.ofComponents
    (fun M => chartSchemeModuleIsoRestrictModule B S hS X M.obj M.property A)
    fun φ => chartSchemeModuleIsoRestrictModule_naturality B S hS X A φ

/-- The components of the natural isomorphism are the chart transport isomorphisms. -/
theorem chartSchemeModuleFunctorIsoRestrictModule_app (A : SmallEtale B S hS X.1)
    (M : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory) :
    (chartSchemeModuleFunctorIsoRestrictModule B S hS X A).app M
      = chartSchemeModuleIsoRestrictModule B S hS X M.obj M.property A := rfl

end AlgebraicGeometry.Space

end
