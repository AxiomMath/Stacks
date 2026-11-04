module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomEquivComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# Transitions, slice objects and charts over a chart of the complement

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals, let `𝒢` be an `𝒪_X`-module and let `A` be an étale scheme chart
of `X`.  This file supplies three identifications that the descent of the chart half of
[Stacks, Tag 07UM] consumes and that nothing in the tree provides.

The first is the compatibility of `AlgebraicGeometry.Space.chartPushFactor` with the transition
maps of the two filtrations it compares: raising the exponent from `k` to `n` and then factoring
is factoring and then raising the exponent.  With it the chart-level direct system
`k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` and the direct system of the first display of [Stacks, Tag 01YB] on the
chart's scheme are identified *as direct systems*, not merely degreewise — which is what step 3
of [Stacks, Tag 07UM] needs, the transition maps being precomposition with monomorphisms and so
not injective.

The second is the identification of the two spellings of the object of the slice of the small
étale site of `X` at `A` which a Zariski open `V` of the chart's scheme cuts out:
`AlgebraicGeometry.Space.openChartOfComparisonOver`, at which the component formula
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply` is stated,
and `Over.mk (openChartInclusion … A V)`, which is the shape the relocalization statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPushBaseChange.lean` produce.

The third is a restatement of the fact that an étale chart of `X` admitting a morphism to the
chart of `X` underlying a chart of `U = X ∖ V(ℐ)` is itself the chart of `X` underlying a chart
of `U`.

## Main definitions

* `AlgebraicGeometry.Space.chartPushHomOfLE` is the chart restriction of the inclusion
  `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`, the transition map of the chart-level filtration.

## Main results

* `Stacks.CategoryTheory.over_ext` and `Stacks.CategoryTheory.over_ext_of_faithful`: two objects
  of a slice category with equal sources and matching structural morphisms are equal, the second
  testing the structural morphisms through a faithful functor.
* `Stacks.SheafOfModules.val_app_hom_apply_congr`: the component of a morphism of sheaves of
  modules at two equal objects of the site, read on a section.
* `AlgebraicGeometry.Space.chartPushFactor_comp_idealPowSmulMap`: **the factorization of the
  chart restriction of `ℐᵏ𝒢 ⟶ 𝒢` commutes with the transition maps of the two filtrations.**
* `AlgebraicGeometry.Space.openChartOfComparisonOver_eq`: **the object of the slice at `A` cut
  out by a Zariski open of the chart's scheme is the chart that open cuts out, with the inclusion
  as its structural morphism.**
* `AlgebraicGeometry.Space.val_app_hom_apply_openChartOfComparisonOver`: the transport of a
  component of a morphism on the slice across that identification, read on a section.
* `AlgebraicGeometry.Space.exists_pc_eq_of_over`: **an étale chart of `X` over the chart of `X`
  underlying a chart of `U = X ∖ V(ℐ)` is itself the chart of `X` underlying a chart of `U`.**

## Implementation notes

**The transition compatibility is proved by cancelling the inclusion of the subsheaf.**  Both
sides are factorizations through `Iᵏ` times the chart restriction of `𝒢` of one and the same
morphism, namely the chart restriction of `ℐⁿ𝒢 ⟶ 𝒢`, so composing with
`Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι` — a monomorphism — reduces the statement
to `AlgebraicGeometry.Space.chartPushFactor_comp_ι`,
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap_comp_ι` and the functoriality of the
pushforward applied to `AlgebraicGeometry.Space.idealPowModuleHomOfLE_comp_ι`.  Every equation is
passed to a `congrArg` rather than rewritten: the two filtrations live in
`AlgebraicGeometry.Scheme.Modules` and in `CategoryTheory.SheafOfModules`, whose `Category`
instances are definitionally equal but not syntactically so, and a rewrite there reports a
missing pattern.

**The slice identification is tested through a faithful functor, and at the scheme level.**  The
two objects have equal sources by
`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`, so the structural morphisms
differ by a `CategoryTheory.eqToHom`, and that `eqToHom` is absorbed by
`CategoryTheory.eqToHom_comp_of_refl` — which needs its source and target to be *definitionally*
equal.  They are at the level of schemes, where the only discrepancy is
`CategoryTheory.Functor.map_preimage` for the inclusion of the size-bounded category of schemes;
one layer up, in the big fppf site, absorbing the same `eqToHom` exhausts the heartbeat budget.
`Stacks.CategoryTheory.over_ext_of_faithful` therefore states the hypothesis with the faithful
functor `SmallEtale.toOver … ⋙ BigFppfOver.toScheme …` already applied.

**The component transport is made on a section.**  The sections of a module on the slice over the
two spellings are modules over two different rings, so an equality of the two objects of the site
does not give an equality of `CategoryTheory.ModuleCat` objects and there is no `eqToHom` to
compose with.  `Stacks.SheafOfModules.val_app_hom_apply_congr` is therefore stated on an element,
where both transports are `cast`s along equalities of types and `Eq.mpr` on the object equality
finishes.

**`AlgebraicGeometry.Space.exists_pc_eq_of_over` duplicates a `private` declaration.**  It is
`exists_pc_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitInjective.lean`, which is `private` there
and therefore cannot be imported.  The public *equality*
`AlgebraicGeometry.Space.exists_pc_eq_openChart` is a different statement: it produces a chart of
`U` for a Zariski open of a chart's scheme lying off the support, whereas this produces one for an
arbitrary chart of `X` over a chart of `U`.

No declaration here carries a `stacks` tag: these are inputs to the reduction of [Stacks, Tag
07UM] to a chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.CategoryTheory

universe v₁ u₁ v₂ u₂

/-- **Two objects of a slice category with equal sources and matching structural morphisms are
equal.**  The structural morphisms are compared after the transport along the equality of the
sources, which is all the comparison there is: the remaining field of a slice object lives in
`PUnit`. -/
theorem over_ext {C : Type u₁} [Category.{v₁} C] {A : C}
    {U V : CategoryTheory.Over A} (h : U.left = V.left) (hw : U.hom = eqToHom h ≫ V.hom) :
    U = V := by
  have key : ∀ {P Q : C} (e : P = Q) (f : P ⟶ A) (g : Q ⟶ A), f = eqToHom e ≫ g →
      CategoryTheory.Over.mk f = CategoryTheory.Over.mk g := by
    intro P Q e f g hfg
    subst e
    rw [eqToHom_refl, Category.id_comp] at hfg
    rw [hfg]
  exact key h U.hom V.hom hw

/-- **`Stacks.CategoryTheory.over_ext` with the structural morphisms compared through a faithful
functor.**  The point is *where* the transport is absorbed: an `eqToHom` between two objects that
are only definitionally equal is absorbed by `CategoryTheory.eqToHom_comp_of_refl`, and whether
that definitional check is affordable depends on the category it is made in. -/
theorem over_ext_of_faithful {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (Fu : C ⥤ D) [Fu.Faithful] {A : C} {U V : CategoryTheory.Over A}
    (h : U.left = V.left)
    (hw : Fu.map U.hom = eqToHom (congrArg Fu.obj h) ≫ Fu.map V.hom) : U = V := by
  refine over_ext h (Fu.map_injective ?_)
  rw [Fu.map_comp, eqToHom_map]
  exact hw

end Stacks.CategoryTheory

namespace Stacks.SheafOfModules

universe w m v₁ u₁

/-- **The component of a morphism of sheaves of modules at two equal objects of the site, read on
a section.**  Both transports are `cast`s along equalities of types, which is the only form in
which they can be compared: the sections over the two objects are modules over two different
rings, so there is no equality of `CategoryTheory.ModuleCat` objects and no
`CategoryTheory.eqToHom` to compose with. -/
theorem val_app_hom_apply_congr {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : CategoryTheory.Sheaf J RingCat.{w}} {M N : _root_.SheafOfModules.{m} R} (α : M ⟶ N)
    {Z Z' : C} (e : Z = Z') (x : (M.val.obj (op Z) : Type m)) :
    (α.val.app (op Z)).hom x =
      cast (congrArg (fun W : C => (N.val.obj (op W) : Type m)) e).symm
        ((α.val.app (op Z')).hom
          (cast (congrArg (fun W : C => (M.val.obj (op W) : Type m)) e) x)) := by
  subst e
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The transition maps of the chart-level filtration -/

/-- The chart restriction of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`, which is the transition map of the
direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` at the chart. -/
abbrev chartPushHomOfLE (I : IdealSheaves B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS X.1 X.2) (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n) :
    chartPush B S hS X (idealPowModule I n G) A ⟶
      chartPush B S hS X (idealPowModule I k G) A :=
  (SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map
    (idealPowModuleHomOfLE I G h)

/-- **The factorization of the chart restriction of `ℐᵏ𝒢 ⟶ 𝒢` commutes with the transition maps
of the two filtrations.**  Factoring at `n` and then lowering the exponent to `k` on the chart's
scheme is lowering it on `X` and then factoring at `k`.

This is what identifies the chart-level direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` with the direct
system of the first display of [Stacks, Tag 01YB] on the chart's scheme *as a direct system*; the
degreewise identification is `AlgebraicGeometry.Space.chartPushFactorIso`. -/
theorem chartPushFactor_comp_idealPowSmulMap (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) {k n : ℕ} (h : k ≤ n) :
    chartPushFactor B S hS X I hIc G hIq hGq A n ≫
        Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
          (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h =
      chartPushHomOfLE B S hS X I G A h ≫
        chartPushFactor B S hS X I hIc G hIq hGq A k := by
  have hι : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
        (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
          (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A)) =
      Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
          (idealSheafDataOfChart B S hS X I hIc A) n (chartPush B S hS X G A)) :=
    Stacks.AlgebraicGeometry.IdealPower.idealPowerMultipleMap_comp_ι _ _ h
  have hmap : chartPushHomOfLE B S hS X I G A h ≫ chartPushι B S hS X I G A k =
      chartPushι B S hS X I G A n :=
    ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map_comp
        (idealPowModuleHomOfLE I G h) (idealPowModuleι I k G)).symm.trans
      (congrArg ((SheafOfModules.pushforward.{u} (chartComparisonRingMap B S hS X A)).map)
        (idealPowModuleHomOfLE_comp_ι I G h))
  refine (cancel_mono (Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
      (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A)))).mp ?_
  rw [Category.assoc, Category.assoc, hι, chartPushFactor_comp_ι, chartPushFactor_comp_ι, hmap]

/-! ### The two spellings of the slice object cut out by a Zariski open -/

/-- **The object of the slice of the small étale site of `X` at a chart which a Zariski open of
the chart's scheme cuts out is the chart that open cuts out, with the inclusion as its structural
morphism.**

The sources agree by `AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`, and the
structural morphisms agree after that transport: tested at the level of schemes, both are the
inclusion of the open, one through `CategoryTheory.Functor.preimage` and the other through
`CategoryTheory.yonedaEquiv`. -/
theorem openChartOfComparisonOver_eq (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    openChartOfComparisonOver B S hS X A V =
      Over.mk (openChartInclusion B S hS X.1 A V) := by
  refine Stacks.CategoryTheory.over_ext_of_faithful
    (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS)
    (openChart_eq_chartLocalization_opensObj B S hS X A V) ?_
  refine Eq.trans ?_ (CategoryTheory.eqToHom_comp_of_refl _ _).symm
  refine Eq.trans ?_ (toScheme_map_toOver_map_openChartInclusion B S hS X.1 A V).symm
  exact congrArg (fun f => (BigFppfOver.toScheme B S hS).map f) (yonedaEquiv_yoneda_map _)

/-- **The transport of a component of a morphism on the slice across
`AlgebraicGeometry.Space.openChartOfComparisonOver_eq`, read on a section.**  This is what lets
the component formula
`AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`, stated at
`AlgebraicGeometry.Space.openChartOfComparisonOver`, be fed to the relocalization statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPushBaseChange.lean`, which name the same object as
`Over.mk (openChartInclusion … A V)`. -/
theorem val_app_hom_apply_openChartOfComparisonOver
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (x : ((M.over A).val.obj (op (openChartOfComparisonOver B S hS X A V)) : Type u)) :
    (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom x =
      cast (congrArg (fun W : CategoryTheory.Over A => ((N.over A).val.obj (op W) : Type u))
          (openChartOfComparisonOver_eq B S hS X A V)).symm
        ((α.val.app (op (Over.mk (openChartInclusion B S hS X.1 A V)))).hom
          (cast (congrArg (fun W : CategoryTheory.Over A =>
              ((M.over A).val.obj (op W) : Type u))
            (openChartOfComparisonOver_eq B S hS X A V)) x)) :=
  Stacks.SheafOfModules.val_app_hom_apply_congr α
    (openChartOfComparisonOver_eq B S hS X A V) x

/-! ### Charts of `X` lying over a chart of the complement -/

/-- **An étale chart of `X` admitting a morphism to the chart of `X` underlying a chart of
`U = X ∖ V(ℐ)` is itself the chart of `X` underlying a chart of `U`.**

The structure morphism of the smaller chart factors through the subfunctor cut out by `U`,
because it factors through the structure morphism of the larger one; the factored morphism is
again a representable étale chart because the inclusion of `U` is a monomorphism.

This is an alias of `exists_pc_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitInjective.lean`. -/
alias exists_pc_eq_of_over := AlgebraicGeometry.Space.exists_pc_eq

end AlgebraicGeometry.Space

end
