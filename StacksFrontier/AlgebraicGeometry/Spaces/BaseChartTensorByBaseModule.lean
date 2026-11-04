module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# Tensoring an `𝒪_X`-module by a module over the coordinate ring of an affine base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and suppose the small étale site of `Y` has a terminal chart `V₀` — as it does when `Y` is
affine, by `AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`.  Then

  `A = Γ(chartScheme V₀, ⊤)`

is the coordinate ring of `Y`, read in the universe `u` of the schemes rather than in the
universe `u + 1` of the compatible families of local sections, and every chart `U` of `X` carries
a ring map `A ⟶ 𝒪_X(U)`: the comparison of global function rings of **Stacks 0732** followed by
restriction of a global function to the chart.  Those maps form a morphism of presheaves of
commutative rings

  `θ : \underline{A} ⟶ 𝒪_X`,

and `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` turns it into the functor
`M ↦ 𝓕 ⊗_A M` on `𝒪_X`-modules.  This is the functor the second part of
[Stacks Project, Tag 073K] runs its dévissage along: there `A` is the coordinate ring of the
affine base `Y = Spec A`, `𝓕` is a quasi-coherent `𝒪_X`-module, and the colimit preservation
below is what turns Lazard's presentation of a flat `A`-module into a presentation of
`𝓕 ⊗_A M`.

**The small étale site of `X` is not assumed to have a terminal chart.**  Only `Y` is, and only
to produce the coordinate ring; `X` is an arbitrary algebraic space, which is why the functor is
taken in the form of `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` — the one that consumes
a morphism of presheaves of rings instead of a terminal object of the site and a ring map into
its sections.

## Main definitions

* `AlgebraicGeometry.Space.baseChartRing`: the coordinate ring `A = Γ(chartScheme V₀, ⊤)` of the
  base at a terminal chart `V₀`, which lies in `Type u`.
* `AlgebraicGeometry.Space.baseChartRingHom`: the ring map `A ⟶ 𝒪_X(U)` at a chart `U` of `X`.
* `AlgebraicGeometry.Space.baseChartCoefficientMap`: **the morphism of presheaves of commutative
  rings `\underline{A} ⟶ 𝒪_X`** assembled from those maps.
* `AlgebraicGeometry.Space.tensorByBaseChartModule`: **the functor `M ↦ 𝓕 ⊗_A M`** from
  `A`-modules in `Type u` to `𝒪_X`-modules on the small étale site.

## Main results

* `AlgebraicGeometry.Space.additive_tensorByBaseChartModule` and
  `AlgebraicGeometry.Space.preservesColimitsOfSize_tensorByBaseChartModule`: the functor is
  additive and preserves colimits of size `{u, u}`, with nothing assumed of `X`.
* `AlgebraicGeometry.Space.tensorByBaseChartModuleUnitIso`: **`𝓕 ⊗_A A ≅ 𝓕`.**

## Implementation notes

*Why the coordinate ring is read at a terminal chart.*  The ring of global regular functions of
an algebraic space is a subring of a product indexed by the objects of its small étale site, and
those lie in `Type (u + 1)`; evaluation at a terminal chart identifies it with the regular
functions on a single scheme, in `Type u`
(`AlgebraicGeometry.Space.globalSectionsChartRingEquiv`).  Both the dévissage of
`Stacks.FlatDevissage.isIso_app_of_flat` and **Stacks 073E** at module universe `u` index by a
category in the universe of the ring, so the coordinate ring has to be read in `Type u`.

*The sections of the structure sheaf over a chart are the regular functions on the chart's
scheme, on the nose.*  `AlgebraicGeometry.Space.structurePresheaf` is
`(SmallEtale.toOver ⋙ BigFppfOver.toScheme).op ⋙ Scheme.Γ`, so the target of
`AlgebraicGeometry.Space.globalFunctionsChartRestriction` is the sections of the structure sheaf
over the chart without any transport, and the restriction maps of the structure sheaf are the
pullbacks of regular functions that
`AlgebraicGeometry.Space.globalFunctionsChartRestriction_naturality` speaks about.  That is what
makes the naturality of `baseChartCoefficientMap` the naturality of restriction of a global
function.

*The two spellings of the sheaf of rings agree on the nose.*
`Stacks.TensorByBaseModule.ringSheaf` of the structure sheaf of the small étale site is
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, so the values of the functor below are
`AlgebraicGeometry.Space.Modules` with no transport; the three site hypotheses that
`Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` carries are all found by instance search for
the small étale topology.

No declaration here carries a `stacks` tag: this is the input to the second part of Tag 073K
rather than an assertion of any tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.TensorByBaseModule

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The coordinate ring of the base at a chart `V₀` of `Y`: the ring of regular functions on the
scheme of that chart.  For a *terminal* chart of an affine `Y` this is the coordinate ring `A`
with `Y = Spec A`, and it lies in `Type u` rather than in the universe `u + 1` of the compatible
families of local sections. -/
abbrev baseChartRing (Y : AlgebraicSpaces B S hS) (V₀ : SmallEtale B S hS Y.1) : Type u :=
  Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V₀), ⊤)

/-- The ring map `A ⟶ 𝒪_X(U)` at a chart `U` of `X`: a regular function on the scheme of the
terminal chart `V₀` of `Y` is a global regular function on `Y` by
`AlgebraicGeometry.Space.globalSectionsChartRingEquiv`, is carried to a global regular function on
`X` by the comparison of **Stacks 0732**, and is restricted to the chart `U`. -/
def baseChartRingHom (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    baseChartRing B S hS Y V₀ →+* (structureSheaf B S hS X.1 X.2).val.obj U :=
  (globalFunctionsChartRestriction B S hS X U.unop).comp
    ((globalSectionsRingHomSite B S hS f).comp
      (globalSectionsChartRingEquiv B S hS Y hV₀).symm.toRingHom)

/-- **The morphism of presheaves of commutative rings `\underline{A} ⟶ 𝒪_X`** attached to a
morphism `f : X ⟶ Y` and a terminal chart of `Y`.

Its naturality is the compatibility of restriction of a global regular function with the
restriction maps of the structure sheaf,
`AlgebraicGeometry.Space.globalFunctionsChartRestriction_naturality`; the restriction maps of the
constant presheaf of rings are identities, so no condition is imposed on the ring map itself. -/
def baseChartCoefficientMap (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀) :
    constantRingPresheaf (C := SmallEtale B S hS X.1) (baseChartRing B S hS Y V₀) ⟶
      (structureSheaf B S hS X.1 X.2).val where
  app U := CommRingCat.ofHom (baseChartRingHom B S hS f hV₀ U)
  naturality {U W} g := by
    refine (Category.id_comp _).trans (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    change globalFunctionsChartRestriction B S hS X W.unop
        ((globalSectionsRingHomSite B S hS f)
          ((globalSectionsChartRingEquiv B S hS Y hV₀).symm a))
      = (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map g.unop)))).hom
            (globalFunctionsChartRestriction B S hS X U.unop
              ((globalSectionsRingHomSite B S hS f)
                ((globalSectionsChartRingEquiv B S hS Y hV₀).symm a)))
    exact (congrFun (globalFunctionsChartRestriction_naturality B S hS X g.unop) _).symm

/-- Over a chart `U`, the coefficient map is `AlgebraicGeometry.Space.baseChartRingHom`. -/
@[simp]
theorem baseChartCoefficientMap_app (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (baseChartCoefficientMap B S hS f hV₀).app U =
      CommRingCat.ofHom (baseChartRingHom B S hS f hV₀ U) :=
  rfl

/-- **Tensoring an `𝒪_X`-module by a module over the coordinate ring of the base**: the functor
`M ↦ 𝓕 ⊗_A M` from `A`-modules in `Type u` to `𝒪_X`-modules on the small étale site of `X`, for
`A` the coordinate ring of `Y` at a terminal chart.

Nothing is assumed of `X`: the construction consumes the morphism of presheaves of rings
`AlgebraicGeometry.Space.baseChartCoefficientMap` and not a terminal chart of `X`, which a
general algebraic space does not have. -/
def tensorByBaseChartModule (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    ModuleCat.{u} (baseChartRing B S hS Y V₀) ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  tensorByBaseModuleOfHom _ (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) 𝓕 (baseChartCoefficientMap B S hS f hV₀)

/-- **`𝓕 ⊗_A (-)` is additive.** -/
instance additive_tensorByBaseChartModule (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    (tensorByBaseChartModule B S hS f hV₀ 𝓕).Additive :=
  tensorByBaseModuleOfHom_additive _ (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) 𝓕 (baseChartCoefficientMap B S hS f hV₀)

/-- **`𝓕 ⊗_A (-)` preserves colimits of size `{u, u}`**, which is what turns a presentation of an
`A`-module into a presentation of `𝓕 ⊗_A M`. -/
instance preservesColimitsOfSize_tensorByBaseChartModule (f : X ⟶ Y)
    {V₀ : SmallEtale B S hS Y.1} (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    PreservesColimitsOfSize.{u, u} (tensorByBaseChartModule B S hS f hV₀ 𝓕) :=
  preservesColimitsOfSize_tensorByBaseModuleOfHom _ (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) 𝓕 (baseChartCoefficientMap B S hS f hV₀)

/-- **`𝓕 ⊗_A A ≅ 𝓕`**: the value of the functor at the free module of rank one is `𝓕` itself.
This is the component of the dévissage at which the comparison of
`Stacks.FlatDevissage.tensorComparisonUniv` has to be shown invertible. -/
def tensorByBaseChartModuleUnitIso (f : X ⟶ Y) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (𝓕 : Modules.{u, u} B S hS X.1 X.2) :
    (tensorByBaseChartModule B S hS f hV₀ 𝓕).obj
        (ModuleCat.of _ (baseChartRing B S hS Y V₀)) ≅ 𝓕 :=
  tensorByBaseModuleOfHomUnitIso _ (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) 𝓕 (baseChartCoefficientMap B S hS f hV₀)

end AlgebraicGeometry.Space

end
