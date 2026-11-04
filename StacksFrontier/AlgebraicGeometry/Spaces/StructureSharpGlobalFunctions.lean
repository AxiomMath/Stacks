module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# Global functions across a morphism whose structure map is an isomorphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` whose
structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 is an isomorphism.  On an étale chart `V` of `Y`
the structure map is the comparison

`𝒪_Y(V) ⟶ lim_{V'} 𝒪_X(V')`

of `AlgebraicGeometry.Space.structureMapApp`, the limit being over the étale charts `V'` of `X`
above the algebraic space `X ×_Y V`, and so its invertibility says exactly that a regular function
on `V` is the same datum as a compatible family of regular functions on those charts.

This file reads that at a chart `V` whose associated algebraic space over `Y` is *the identity* —
for instance the identity chart of the algebraic space represented by a scheme.  Then `X ×_Y V`
is a terminal object of the spaces-étale site of `X`, so the index category of the limit is the
whole small étale site of `X` and the limit is the ring `AlgebraicGeometry.Space.globalFunctions`
of global regular functions of `X`:

`𝒪_Y(V) ≃+* H⁰(X, 𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.terminalChartIndex`: the arrow from an étale chart of `X` into the
  cartesian base change `X ×_Y V`, which is unique because that base change is terminal.
* `AlgebraicGeometry.Space.terminalChartPullback`: **the comparison itself**, the ring
  homomorphism `𝒪_Y(V) ⟶ H⁰(X, 𝒪_X)` which on each étale chart of `X` is pullback of regular
  functions along the induced morphism of schemes.
* `AlgebraicGeometry.Space.terminalChartPullbackRingEquiv` and
  `AlgebraicGeometry.Space.schemeChartGlobalFunctionsRingEquiv`: that homomorphism as an
  isomorphism of rings, the second one for a morphism `X ⟶ U₀` to the algebraic space represented
  by a scheme over the base, where the chart is the identity chart of `U₀` and the source of the
  comparison is `Γ(U₀, 𝒪_{U₀})`.

## Main results

* `AlgebraicGeometry.Space.bijective_structureMapApp`: if the structure map is an isomorphism of
  sheaves of rings then it is bijective on sections over every étale chart of `Y`.
* `AlgebraicGeometry.Space.isTerminal_chartBaseChange_of_isIso`: the cartesian base change of a
  chart of `Y` whose associated algebraic space over `Y` is an isomorphism is a terminal object of
  the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.bijective_terminalChartPullback`: **the comparison is bijective**, so
  that the regular functions on such a chart of `Y` are the global regular functions of `X`.

## Implementation notes

The comparison is built chartwise from `AlgebraicGeometry.Space.chartPullbackRingHom`, the form
that `AlgebraicGeometry.Space.chartProjection_structureMapApp` compares with the structure map,
and not as `AlgebraicGeometry.Space.globalFunctionsMap`. The two are compatible, but that is not
proved here.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)

/-! ### The structure map is bijective on sections -/

/-- **An invertible structure map is bijective on the sections over an étale chart of `Y`.** -/
theorem bijective_structureMapApp (hf : IsIso (structureSharp B S hS f)) :
    Function.Bijective (structureMapApp B S hS f V) := by
  have key : ∀ a, ((structureSharp B S hS f).hom.app (op V)).hom a =
      ((smallEtaleDirectImageRanIso B S hS f).inv.app
        (structureSetSheaf B S hS X)).hom.app (op V)
        (structureMapApp B S hS f V a) := fun _ ↦ rfl
  have h1 : Function.Bijective
      (fun a ↦ ((structureSharp B S hS f).hom.app (op V)).hom a) :=
    ConcreteCategory.bijective_of_isIso ((structureSharp B S hS f).hom.app (op V))
  set i := (smallEtaleDirectImageRanIso B S hS f).symm.app (structureSetSheaf B S hS X) with hi
  have h2 : Function.Bijective (fun b ↦ i.hom.hom.app (op V) b) :=
    ConcreteCategory.bijective_of_isIso (i.hom.hom.app (op V))
  refine ⟨fun a b hab ↦ h1.1 ((key a).trans ((congrArg _ hab).trans (key b).symm)), fun y ↦ ?_⟩
  obtain ⟨a, ha⟩ := h1.2 (i.hom.hom.app (op V) y)
  exact ⟨a, h2.1 ((key a).symm.trans ha)⟩

/-! ### A chart of `Y` which is the identity -/

variable (hV : IsIso ((comparisonFunctor B S hS Y).obj V).1.hom)

/-- **The cartesian base change of an identity chart is terminal.**  If the algebraic space over
`Y` attached to the étale chart `V` by Stacks 03G1 has an invertible structure morphism, then its
base change along `f` is a terminal object of the spaces-étale site of `X`. -/
noncomputable def isTerminal_chartBaseChange_of_isIso :
    IsTerminal (chartBaseChange B S hS f V) :=
  haveI := hV
  SpacesEtale.isTerminal_of_isIso B S hS _
    (((spacesBaseChange B S hS f).isPullback
      ((comparisonFunctor B S hS Y).obj V)).isIso_snd_of_isIso)

/-- The index of the limit computing the sections of the direct image over `V` attached to an
étale chart `U` of `X`: the unique arrow from `U` into the terminal object `X ×_Y V` of the
spaces-étale site of `X`. -/
noncomputable def terminalChartIndex (U : SmallEtale B S hS X.1) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk ((isTerminal_chartBaseChange_of_isIso B S hS f V hV).from
    ((comparisonFunctor B S hS X).obj U)).op

/-- **The morphism of schemes attached to an index of the limit depends only on its chart**: it
is the one attached to the index `AlgebraicGeometry.Space.terminalChartIndex` of that chart. -/
theorem chartBaseChangeMap_terminalChartIndex
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    chartBaseChangeMap B S hS f V j =
      chartBaseChangeMap B S hS f V (terminalChartIndex B S hS f V hV j.right.unop) := by
  have h : j.hom.unop = (terminalChartIndex B S hS f V hV j.right.unop).hom.unop :=
    (isTerminal_chartBaseChange_of_isIso B S hS f V hV).hom_ext _ _
  simp only [chartBaseChangeMap]
  rw [h]
  rfl

/-- Pullback of regular functions to an étale chart of `X` does not depend on the index of the
limit, only on the chart. -/
theorem chartPullback_terminalChartIndex
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    chartPullback B S hS f V j a =
      chartPullbackRingHom B S hS f V (terminalChartIndex B S hS f V hV j.right.unop) a :=
  congrArg (fun m ↦ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom a)
    (chartBaseChangeMap_terminalChartIndex B S hS f V hV j)

/-! ### The regular functions on the chart as the global functions of `X` -/

/-- **Pullback of the regular functions on an identity chart `V` of `Y` to the global regular
functions of `X`**: a function on `V` goes to the family of its pullbacks along the morphisms of
schemes `U ⟶ V` induced by the étale charts `U` of `X`. -/
noncomputable def terminalChartPullback :
    ToType ((structureRingSheaf B S hS Y).obj.obj (op V)) →+* globalFunctions B S hS X.1 where
  toFun a := ⟨fun U ↦ chartPullbackRingHom B S hS f V
      (terminalChartIndex B S hS f V hV U.unop) a, by
    intro U W h
    exact (congrArg (fun φ ↦ φ a) (chartPullback_comp B S hS f V
      (j₁ := terminalChartIndex B S hS f V hV U.unop)
      (j₂ := terminalChartIndex B S hS f V hV W.unop)
      (StructuredArrow.homMk h (Quiver.Hom.unop_inj
        ((isTerminal_chartBaseChange_of_isIso B S hS f V hV).hom_ext _ _))))).symm⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' a b := Subtype.ext (funext fun _ ↦ map_mul _ a b)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' a b := Subtype.ext (funext fun _ ↦ map_add _ a b)

/-- **The regular functions on an identity chart of `Y` are the global regular functions of `X`,
when the structure map of `f` is an isomorphism.** -/
theorem bijective_terminalChartPullback (hf : IsIso (structureSharp B S hS f)) :
    Function.Bijective (terminalChartPullback B S hS f V hV) := by
  have hb := bijective_structureMapApp B S hS f V hf
  refine ⟨fun a b hab ↦ hb.1 (chartProjection_ext B S hS f V (fun j ↦ ?_)), fun c ↦ ?_⟩
  · refine (chartProjection_structureMapApp B S hS f V j a).trans
      (Eq.trans ?_ (chartProjection_structureMapApp B S hS f V j b).symm)
    refine (chartPullback_terminalChartIndex B S hS f V hV j a).trans
      (Eq.trans ?_ (chartPullback_terminalChartIndex B S hS f V hV j b).symm)
    exact congrFun (congrArg Subtype.val hab) j.right
  · obtain ⟨a, ha⟩ := hb.2 ((Types.isLimitEquivSections (chartIsLimit B S hS f V)).symm
      ⟨fun j ↦ c.val j.right, fun {_ _} φ ↦ c.property φ.right⟩)
    refine ⟨a, Subtype.ext (funext fun U ↦ ?_)⟩
    refine (chartProjection_structureMapApp B S hS f V
      (terminalChartIndex B S hS f V hV U.unop) a).symm.trans ?_
    refine (congrArg (fun z ↦ (chartProjection B S hS f V
      (terminalChartIndex B S hS f V hV U.unop)).app (structureSetSheaf B S hS X) z) ha).trans ?_
    refine (chartProjection_app_apply B S hS f V
      (terminalChartIndex B S hS f V hV U.unop) _).trans ?_
    exact congrFun (congrArg Subtype.val
      ((Types.isLimitEquivSections (chartIsLimit B S hS f V)).apply_symm_apply
        ⟨fun j ↦ c.val j.right, fun {_ _} φ ↦ c.property φ.right⟩))
      (terminalChartIndex B S hS f V hV U.unop)

/-- **The comparison of `AlgebraicGeometry.Space.terminalChartPullback` as an isomorphism of
rings**: if the structure map of `f` is an isomorphism then the regular functions on an identity
chart `V` of `Y` are the global regular functions of `X`. -/
noncomputable def terminalChartPullbackRingEquiv (hf : IsIso (structureSharp B S hS f)) :
    ToType ((structureRingSheaf B S hS Y).obj.obj (op V)) ≃+* globalFunctions B S hS X.1 :=
  RingEquiv.ofBijective _ (bijective_terminalChartPullback B S hS f V hV hf)

/-! ### The case of a morphism to the algebraic space of a scheme -/

/-- **The global regular functions of an algebraic space over a scheme whose structure map is an
isomorphism are the regular functions on that scheme.** For a morphism `f : X ⟶ U₀` of algebraic
spaces whose target is the algebraic space represented by a scheme `U₀` over the base, this is
`AlgebraicGeometry.Space.terminalChartPullbackRingEquiv` at the identity chart
`AlgebraicGeometry.Space.idEtaleChart` of `U₀`, a ring isomorphism
`Γ(U₀, 𝒪_{U₀}) ≃+* H⁰(X, 𝒪_X)`. -/
noncomputable def schemeChartGlobalFunctionsRingEquiv {X : AlgebraicSpaces B S hS}
    (U₀ : BigFppfOver B S hS) (f : X ⟶ (schemeSpaceFunctor B S hS).obj U₀)
    (hf : IsIso (structureSharp B S hS f)) :
    ToType (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj U₀))) ≃+*
      globalFunctions B S hS X.1 :=
  terminalChartPullbackRingEquiv B S hS f (idEtaleChart B S hS U₀)
    (by change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj U₀)); infer_instance) hf

end AlgebraicGeometry.Space

end
