module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSemilinear

/-!
# Naturality in the module of the chart sections identification

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `A` be an
étale scheme chart of `X` and let `W` be a Zariski open of the chart's scheme.
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` identifies the sections over `W` of the chart
restriction of a quasi-coherent `𝒪_X`-module with the sections of that module over the étale
chart which `W` cuts out.  It is defined objectwise, and nothing says that it is natural in the
module: `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` is naturality of
the isomorphism of *sheaves* and never evaluates the identification on sections, so a morphism of
`𝒪_X`-modules — such as the inclusion of a submodule — cannot be pushed through the
identification at all.

This file supplies that naturality.  The chart restriction is a chain of four
`CategoryTheory.SheafOfModules.pushforward`s, and a pushforward does nothing to a morphism on
sections except restrict the scalars it is linear over; so the square commutes definitionally,
and all the work is in presenting the chain to a generic statement of that fact.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsMap`: the chart restriction of a morphism of
  quasi-coherent `𝒪_X`-modules, read on sections over a Zariski open of the chart's scheme.

## Main results

* `Stacks.SheafOfModules.pushforward_four_obj_val_obj`: **four pushforwards of sheaves of modules
  collapse, on sections, to one restriction of scalars** along the composite of the four structure
  maps.
* `Stacks.SheafOfModules.pushforward_four_map_val_app`: **the collapse is natural in the module**
  — the square built from a morphism of sheaves of modules, its image under the four
  pushforwards, and the two collapse identifications commutes.
* `AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor_map_eq_pushforward`: the chart transport
  of a morphism of quasi-coherent `𝒪_X`-modules, written as four pushforwards of that morphism.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality` and
  `AlgebraicGeometry.Space.chartSectionsMap_naturality`: **the chart sections identification is
  natural in the module** — over a Zariski open `W` of the chart's scheme, the chart restriction
  of a morphism `φ` of quasi-coherent `𝒪_X`-modules followed by the identification at the target
  is the identification at the source followed by `φ` on sections over the étale chart which `W`
  cuts out.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality_apply`: **the same read on a
  section** — `AlgebraicGeometry.Space.chartSectionsLinearEquiv` of the chart restriction of `φ`
  applied to a section is `φ` over the étale chart applied to
  `AlgebraicGeometry.Space.chartSectionsLinearEquiv` of that section.  This is the statement which
  the reduction of Stacks 07UM to a chart needs for the inclusion `ℐⁿ𝒢 ⟶ 𝒢`.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_eq_eqToIso`,
  `AlgebraicGeometry.Space.chartSectionsLinearEquiv_toLinearMap`,
  `AlgebraicGeometry.Space.chartSectionsLinearEquiv_apply_eqToIso` and
  `AlgebraicGeometry.Space.chartSectionsLinearEquiv_apply`: the transport appearing in the square
  is `AlgebraicGeometry.Space.chartSectionsLinearEquiv` — read as an isomorphism, as a linear map,
  and on a section.

## Implementation notes

**Everything generic is `rfl`, and every chart-level statement is an instantiation of a generic
one.**  Both statements in `Stacks.SheafOfModules`, and all three in `Stacks.ModuleCat`, hold by
`rfl` for bare chains of morphisms and abstract modules, where the definitional check is small.
At the chart the same checks exhaust the heartbeat budget, so nothing below is proved by `rfl`:
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality` is the generic square with the
chart's four structure maps substituted, and the two identity structure maps are written the way
`AlgebraicGeometry.Space.chartSchemeRestrictionFunctor` writes them — with
`AlgebraicGeometry.Space.isContinuous_chartLocalization_chartSpace` passed by name — since `𝟙` of
the chart's structure sheaf of rings does not elaborate against the expected type.

**The generic square takes the chain morphism, the image object and the composite ring map as
parameters with equations, and that is what brings it inside the budget.**  Stated with the
canonical composites in place, the chart instantiation costs about 271000 heartbeats, all of it in
matching the conclusion: the two `CategoryTheory.eqToHom`s carry the image object and the
composite ring map in their types, and each occurrence is then a separate definitional check of
the whole four-layer chain.  Passing `P`, `g` and the chain morphism as parameters makes those
occurrences syntactically the chart's own spellings —
`AlgebraicGeometry.Space.openChartOfComparison`,
`AlgebraicGeometry.Space.chartSectionsRingHom` and
`AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor` — and the cost falls to about 87000.

**Reading the square on a section needs the two spellings of the chart transport to be aligned
first, and that is what `AlgebraicGeometry.Space.chartSectionsMap` is for.**  The chart transport
of a module appears in two definitionally equal spellings,
`AlgebraicGeometry.Space.chartSchemeEtaleModule` and
`(AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor …).obj`; the chain morphism has the second
as its codomain and the identification has the first as its domain.  Splitting the composite of
the two on a section — `(f ≫ eqToHom h).hom x = (eqToHom h).hom (f.hom x)` — then costs the
budget, whereas the same step on the other side of the square, where no such mismatch occurs, is
immediate.  `AlgebraicGeometry.Space.chartSectionsMap` is the chain morphism *declared* at the
first spelling, which pays that mismatch once; after it every step is syntactic.

**Each applied comparison is obtained from the unapplied one, never directly.**  `rfl` for
`chartSectionsLinearEquiv … y = (eqToHom …).hom y` costs the budget, while the unapplied
`chartSectionsLinearEquiv … = (eqToIso …).toLinearEquiv` is immediate;
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_apply` therefore goes through
`DFunLike.congr_fun`, and the square is read on a section through `congrArg` to
`CategoryTheory.ModuleCat.Hom.hom` followed by `DFunLike.congr_fun`.

No hypothesis beyond quasi-coherence of the modules is carried — and that only because forming
the chart restriction of a module needs it — and no declaration here carries a `stacks` tag: this
is an input to the reduction of Stacks 07UM to a chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

universe w m v₀ v₁ v₂ v₃ v₄ u₀ u₁ u₂ u₃ u₄

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {J₃ : GrothendieckTopology C₃} {J₄ : GrothendieckTopology C₄}
  {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₂} {F₃ : C₂ ⥤ C₃} {F₄ : C₃ ⥤ C₄}
  [inst₁ : F₁.IsContinuous J₀ J₁] [inst₂ : F₂.IsContinuous J₁ J₂]
  [inst₃ : F₃.IsContinuous J₂ J₃] [inst₄ : F₄.IsContinuous J₃ J₄]
  {R₀ : CategoryTheory.Sheaf J₀ RingCat.{w}} {R₁ : CategoryTheory.Sheaf J₁ RingCat.{w}}
  {R₂ : CategoryTheory.Sheaf J₂ RingCat.{w}} {R₃ : CategoryTheory.Sheaf J₃ RingCat.{w}}
  {R₄ : CategoryTheory.Sheaf J₄ RingCat.{w}}
  (φ₁ : R₀ ⟶ (F₁.sheafPushforwardContinuous RingCat.{w} J₀ J₁).obj R₁)
  (φ₂ : R₁ ⟶ (F₂.sheafPushforwardContinuous RingCat.{w} J₁ J₂).obj R₂)
  (φ₃ : R₂ ⟶ (F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃)
  (φ₄ : R₃ ⟶ (F₄.sheafPushforwardContinuous RingCat.{w} J₃ J₄).obj R₄)

/-- **Four pushforwards of sheaves of modules collapse to one restriction of scalars.**  The
sections over `A` of the direct image of `N` along four continuous functors and four morphisms of
sheaves of rings are the sections of `N` over the fourfold image of `A`, with scalars restricted
along the composite of the four structure maps.

This is the shape in which the chart restriction of a module is read off at an object without
re-elaborating the whole chain: the statement is about a bare chain of morphisms of sheaves of
rings and an abstract sheaf of modules, so the definitional check it performs is small. -/
theorem pushforward_four_obj_val_obj (N : _root_.SheafOfModules.{m} R₄) (A : C₀) :
    ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m} φ₃).obj
            ((_root_.SheafOfModules.pushforward.{m} φ₄).obj N)))).val.obj (op A) =
      (ModuleCat.restrictScalars
          ((φ₄.hom.app (op (F₃.obj (F₂.obj (F₁.obj A))))).hom.comp
            ((φ₃.hom.app (op (F₂.obj (F₁.obj A)))).hom.comp
              ((φ₂.hom.app (op (F₁.obj A))).hom.comp (φ₁.hom.app (op A)).hom)))).obj
        (N.val.obj (op (F₄.obj (F₃.obj (F₂.obj (F₁.obj A)))))) := rfl

/-- **The fourfold collapse of pushforwards is natural in the module.**  For a morphism `f` of
sheaves of modules, the image of `f` under the four pushforwards, read on sections over `A` and
followed by the collapse at the target, is the collapse at the source followed by `f` on sections
over the fourfold image of `A`, with its scalars restricted.

The chain morphism `k`, the image object `P` and the composite ring map `g` are parameters with
equations rather than the composites themselves: an instantiation of this statement has to match
its conclusion, and each occurrence of `P` or `g` inside a `CategoryTheory.eqToHom` would
otherwise be a separate definitional check of the whole chain. -/
theorem pushforward_four_map_val_app {M N : _root_.SheafOfModules.{m} R₄} (f : M ⟶ N) (A : C₀)
    (k : (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m} φ₃).obj
            ((_root_.SheafOfModules.pushforward.{m} φ₄).obj M)) ⟶
        (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m} φ₃).obj
            ((_root_.SheafOfModules.pushforward.{m} φ₄).obj N)))
    (hk : k = (_root_.SheafOfModules.pushforward.{m} φ₂).map
      ((_root_.SheafOfModules.pushforward.{m} φ₃).map
        ((_root_.SheafOfModules.pushforward.{m} φ₄).map f)))
    (P : C₄) (hP : F₄.obj (F₃.obj (F₂.obj (F₁.obj A))) = P)
    (g : R₀.obj.obj (op A) →+* R₄.obj.obj (op P))
    (hg : g = hP ▸ ((φ₄.hom.app (op (F₃.obj (F₂.obj (F₁.obj A))))).hom.comp
      ((φ₃.hom.app (op (F₂.obj (F₁.obj A)))).hom.comp
        ((φ₂.hom.app (op (F₁.obj A))).hom.comp (φ₁.hom.app (op A)).hom))))
    (hM : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m} φ₃).obj
            ((_root_.SheafOfModules.pushforward.{m} φ₄).obj M)))).val.obj (op A) =
      (ModuleCat.restrictScalars g).obj (M.val.obj (op P)))
    (hN : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m} φ₃).obj
            ((_root_.SheafOfModules.pushforward.{m} φ₄).obj N)))).val.obj (op A) =
      (ModuleCat.restrictScalars g).obj (N.val.obj (op P))) :
    ((_root_.SheafOfModules.pushforward.{m} φ₁).map k).val.app (op A) ≫ eqToHom hN =
      eqToHom hM ≫ (ModuleCat.restrictScalars g).map (f.val.app (op P)) := by
  subst hP
  subst hk
  subst hg
  rfl

end Stacks.SheafOfModules

namespace Stacks.ModuleCat

universe v w

/-- An equality of objects of `CategoryTheory.ModuleCat`, read as a linear equivalence and
evaluated on an element, is the `CategoryTheory.eqToHom` of that equality applied to it. -/
theorem eqToIso_toLinearEquiv_apply {R : RingCat.{w}} {U V : _root_.ModuleCat.{v} ↑R}
    (h : U = V) (y : U) : (eqToIso h).toLinearEquiv y = (eqToHom h).hom y := rfl

/-- A composite of morphisms of modules, applied to an element. -/
theorem comp_hom_apply {R : RingCat.{w}} {U V V' : _root_.ModuleCat.{v} ↑R} (f : U ⟶ V)
    (g : V ⟶ V') (x : U) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

/-- A transport along an equality of modules followed by a restriction of scalars of a morphism,
applied to an element: the restriction of scalars leaves the underlying map alone. -/
theorem eqToHom_comp_restrictScalars_map_hom_apply {R R' : RingCat.{w}} (g : ↑R →+* ↑R')
    {U : _root_.ModuleCat.{v} ↑R} {U' V' : _root_.ModuleCat.{v} ↑R'}
    (h : U = (_root_.ModuleCat.restrictScalars g).obj U') (β : U' ⟶ V') (x : U) :
    (eqToHom h ≫ (_root_.ModuleCat.restrictScalars g).map β).hom x = β.hom ((eqToHom h).hom x) :=
  rfl

end Stacks.ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The chart transport of a morphism as four pushforwards -/

/-- **The chart transport of a morphism of quasi-coherent `𝒪_X`-modules is the image of that
morphism under four pushforwards of sheaves of modules**: the restriction to the slice of the
small étale site of `X` at the chart, the localization of Stacks 04M0, the inverse of the
comparison of the two small étale sites, and the inclusion of the small Zariski site — of which
this records the inner three, the fourth being `AlgebraicGeometry.SmallEtale.restrictModule`.

The two identity structure maps are written as
`AlgebraicGeometry.Space.chartSchemeRestrictionFunctor` writes them, with the continuity of
the comparison functor passed by name: `𝟙` of the chart's structure sheaf of rings does not
elaborate against the expected type. -/
theorem chartSchemeEtaleModuleFunctor_map_eq_pushforward (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q) :
    (chartSchemeEtaleModuleFunctor B S hS X A).map φ =
      (SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
          (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).map
        ((@SheafOfModules.pushforward _ _ _ _
            (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
            ((SmallEtale.topology B S hS X.1).over A)
            (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor
            (chartStructureRingSheaf B S hS X A)
            ((structureRingSheaf B S hS X).over A)
            (isContinuous_chartLocalization_chartSpace B S hS X A)
            (𝟙 _)).map
          ((@SheafOfModules.pushforward _ _ _ _
              ((SmallEtale.topology B S hS X.1).over A)
              (SmallEtale.topology B S hS X.1)
              (CategoryTheory.Over.forget A)
              ((structureRingSheaf B S hS X).over A)
              (structureRingSheaf B S hS X)
              inferInstance
              (𝟙 _)).map φ.hom)) := rfl

/-! ### Naturality of the chart sections identification -/

/-- **The chart sections identification is natural in the module.**  Let `φ` be a morphism of
quasi-coherent `𝒪_X`-modules and let `W` be a Zariski open of the chart's scheme.  Then the chart
restriction of `φ`, read on sections over `W` and followed by the identification of those
sections at the target, is the identification at the source followed by `φ` on sections over the
étale chart which `W` cuts out, with scalars restricted along
`AlgebraicGeometry.Space.chartSectionsRingHom`.

The two transports are the `CategoryTheory.eqToHom` of
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat`, that is, the
forward map of `AlgebraicGeometry.Space.chartSectionsLinearEquiv`; see
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_eq_eqToIso`.

This is what the reduction of Stacks 07UM to a chart needs for the inclusion of the power of a
sheaf of ideals: without it the sections of `ℐⁿ𝒢` over the comparison chart are invisible on the
chart's scheme, `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` being
naturality of the isomorphism of sheaves and never evaluating the identification on sections. -/
theorem chartSectionsLinearEquiv_naturality (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) (chartFppfObject B S hS X A).left.property).map
          ((chartSchemeEtaleModuleFunctor B S hS X A).map φ)).val.app (op W) ≫
        eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X Q.obj
          Q.property A W) =
      eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X P.obj
          P.property A W) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).map
          (φ.hom.val.app (op (openChartOfComparison B S hS X A W))) :=
  Stacks.SheafOfModules.pushforward_four_map_val_app
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property)
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))
    (J₂ := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
    (C₃ := CategoryTheory.Over A)
    (J₃ := (SmallEtale.topology B S hS X.1).over A)
    (F₃ := (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor)
    (R₃ := (structureRingSheaf B S hS X).over A)
    (inst₃ := isContinuous_chartLocalization_chartSpace B S hS X A)
    (φ₃ := 𝟙 _)
    (C₄ := SmallEtale B S hS X.1)
    (J₄ := SmallEtale.topology B S hS X.1)
    (F₄ := CategoryTheory.Over.forget A)
    (R₄ := structureRingSheaf B S hS X)
    (φ₄ := 𝟙 _)
    (f := φ.hom) (A := W)
    (k := (chartSchemeEtaleModuleFunctor B S hS X A).map φ)
    (hk := chartSchemeEtaleModuleFunctor_map_eq_pushforward B S hS X A φ)
    (P := openChartOfComparison B S hS X A W) (hP := rfl)
    (g := chartSectionsRingHom B S hS X A W) (hg := rfl)
    (hM := restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X P.obj P.property A W)
    (hN := restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X Q.obj Q.property A W)

/-- **The chart restriction of a morphism of quasi-coherent `𝒪_X`-modules, on sections over a
Zariski open of the chart's scheme.**

This is the component at `W` of the chart transport of `φ`, *declared* at the spelling
`AlgebraicGeometry.Space.chartSchemeEtaleModule` of the chart transport of the modules rather
than at `(AlgebraicGeometry.Space.chartSchemeEtaleModuleFunctor …).obj`: the two are
definitionally equal, and paying that here once is what lets the naturality square be read on a
section at all. -/
noncomputable def chartSectionsMap (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X P.obj P.property A)).val.obj (op W) ⟶
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X Q.obj Q.property A)).val.obj (op W) :=
  ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property).map
    ((chartSchemeEtaleModuleFunctor B S hS X A).map φ)).val.app (op W)

/-- `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality` at
`AlgebraicGeometry.Space.chartSectionsMap`: the same square, with every object of the two
composites spelled by the objectwise chart transport. -/
theorem chartSectionsMap_naturality (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens) :
    chartSectionsMap B S hS X A φ W ≫
        eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X Q.obj
          Q.property A W) =
      eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X P.obj
          P.property A W) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).map
          (φ.hom.val.app (op (openChartOfComparison B S hS X A W))) :=
  chartSectionsLinearEquiv_naturality B S hS X A φ W

/-- The left-hand composite of `AlgebraicGeometry.Space.chartSectionsMap_naturality`, read on a
section. -/
theorem chartSectionsMap_comp_eqToHom_apply (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens)
    (x : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X P.obj P.property A)).val.obj (op W)) :
    (chartSectionsMap B S hS X A φ W ≫
        eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X Q.obj
          Q.property A W)).hom x =
      (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X Q.obj
        Q.property A W)).hom ((chartSectionsMap B S hS X A φ W).hom x) :=
  Stacks.ModuleCat.comp_hom_apply _ _ x

/-- The right-hand composite of `AlgebraicGeometry.Space.chartSectionsMap_naturality`, read on a
section. -/
theorem eqToHom_comp_restrictScalars_map_apply (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens)
    (x : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X P.obj P.property A)).val.obj (op W)) :
    (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X P.obj
          P.property A W) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A W)).map
          (φ.hom.val.app (op (openChartOfComparison B S hS X A W)))).hom x =
      (φ.hom.val.app (op (openChartOfComparison B S hS X A W))).hom
        ((eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X P.obj
          P.property A W)).hom x) :=
  Stacks.ModuleCat.eqToHom_comp_restrictScalars_map_hom_apply _ _ _ x

/-! ### The transport of the square is the chart sections linear equivalence -/

variable (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-- The chart sections identification is the `CategoryTheory.eqToIso` of the module-level
identification of its sections, read as a linear equivalence: this is its definition, recorded so
that the transport in `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality` can be
recognized. -/
theorem chartSectionsLinearEquiv_eq_eqToIso (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    chartSectionsLinearEquiv B S hS X M hM A W =
      (eqToIso (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W)
        ).toLinearEquiv := rfl

/-- The chart sections identification, as a linear map, is the `CategoryTheory.eqToHom` of the
module-level identification of its sections — the transport appearing in
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality`. -/
theorem chartSectionsLinearEquiv_toLinearMap (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    (chartSectionsLinearEquiv B S hS X M hM A W).toLinearMap =
      (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W)).hom :=
  rfl

/-- The chart sections identification on a section is the `CategoryTheory.eqToIso` of the
module-level identification applied to it.

This is `AlgebraicGeometry.Space.chartSectionsLinearEquiv_eq_eqToIso` read on an element through
`DFunLike.congr_fun`, and not by `rfl`: comparing the two spellings *after* applying them costs
the heartbeat budget, while comparing the unapplied maps is immediate. -/
theorem chartSectionsLinearEquiv_apply_eqToIso (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op W)) :
    chartSectionsLinearEquiv B S hS X M hM A W y =
      (eqToIso (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W)
        ).toLinearEquiv y :=
  DFunLike.congr_fun (chartSectionsLinearEquiv_eq_eqToIso B S hS X M hM A W) y

/-- **The chart sections identification on a section is the transport appearing in
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality`**, applied to that section.

This is the bridge which lets the naturality square be read on a section: the square is stated
with the `CategoryTheory.eqToHom` of
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat`, and this says that
that morphism and the linear equivalence agree on every section. -/
theorem chartSectionsLinearEquiv_apply (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op W)) :
    chartSectionsLinearEquiv B S hS X M hM A W y =
      (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W)).hom y :=
  (chartSectionsLinearEquiv_apply_eqToIso B S hS X M hM A W y).trans
    (Stacks.ModuleCat.eqToIso_toLinearEquiv_apply
      (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A W) y)

/-! ### Naturality on sections -/

/-- **Naturality in the module of the chart sections identification, read on a section.**  Let
`φ` be a morphism of quasi-coherent `𝒪_X`-modules, let `W` be a Zariski open of the chart's
scheme and let `x` be a section over `W` of the chart restriction of the source.  Then the chart
sections identification at the target, applied to the chart restriction of `φ` of `x`, is `φ` on
sections over the étale chart which `W` cuts out, applied to the chart sections identification at
the source of `x`.

For the inclusion `ℐⁿ𝒢 ⟶ 𝒢` this says that the sections of `ℐⁿ𝒢` over a Zariski open of the
chart's scheme are, under the identification, the sections of `𝒢` over the comparison chart which
come from `ℐⁿ𝒢` there — which is what the reduction of Stacks 07UM to a chart needs and what
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality`, being naturality of an
isomorphism of sheaves, does not give. -/
theorem chartSectionsLinearEquiv_naturality_apply (A : SmallEtale B S hS X.1)
    {P Q : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : P ⟶ Q)
    (W : (chartScheme A).Opens)
    (x : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X P.obj P.property A)).val.obj (op W)) :
    chartSectionsLinearEquiv B S hS X Q.obj Q.property A W
        ((chartSectionsMap B S hS X A φ W).hom x) =
      (φ.hom.val.app (op (openChartOfComparison B S hS X A W))).hom
        (chartSectionsLinearEquiv B S hS X P.obj P.property A W x) :=
  ((chartSectionsLinearEquiv_apply B S hS X Q.obj Q.property A W
        ((chartSectionsMap B S hS X A φ W).hom x)).trans
      ((chartSectionsMap_comp_eqToHom_apply B S hS X A φ W x).symm.trans
        ((DFunLike.congr_fun
            (congrArg ModuleCat.Hom.hom (chartSectionsMap_naturality B S hS X A φ W)) x).trans
          (eqToHom_comp_restrictScalars_map_apply B S hS X A φ W x)))).trans
    (congrArg (φ.hom.val.app (op (openChartOfComparison B S hS X A W))).hom
      (chartSectionsLinearEquiv_apply B S hS X P.obj P.property A W x).symm)

end AlgebraicGeometry.Space

end
