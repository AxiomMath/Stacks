module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartModels
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexChart

/-!
# The two affine modelling predicates agree at the standard model

The repository carries two predicates for "the complex `K` restricted to the affine open `U` is
the associated sheaf of `ω ∈ D(Γ(X, U))`":

* `Stacks.Duality.IsTildeModelOnAnyModel`, with the model of `D(𝒪_X)` a free
  `CategoryTheory.HasDerivedCategory` binder, which is the form in which the affine chart
  description of `f^!` is stated and proved;
* `Stacks.Duality.IsTildeModelOn`, with that model pinned to
  `CategoryTheory.HasDerivedCategory.standard`, which is the form in which the dualizing-complex
  statements that consume a chart description are phrased, because
  `Stacks.Duality.HasDualizingModelOn` seals that model inside its body.

The two definitions are otherwise the same text, so the second is the first at one instance. That
is what this file records, and nothing here has any mathematical content beyond it: every proof is
`rfl`.

What it buys is that a chart description proved with the model left free — the shape
`Stacks.Duality.HasUpperShriekCharts` — can be read, at the standard model, as the hypothesis
shape that `Stacks.Duality.isDualizingComplex_upperShriek_of_fts` asks of its `f^!` parameter.
That reading is `Stacks.Duality.isTildeModelOn_charts_of_hasUpperShriekCharts` below, which is an
identity of statements rather than a derivation.

## Main results

All in the namespace `Stacks.Duality`.

* `isTildeModelOnAnyModel_standard_eq` — the two predicates are *equal as functions* once the
  model binder of the first is instantiated at `HasDerivedCategory.standard`. This is the form to
  `rw` with when the predicate occurs under binders.
* `isTildeModelOnAnyModel_standard_iff` — the same comparison pointwise, as an `Iff`, so both
  directions are available; `IsTildeModelOn.isTildeModelOnAnyModel` and
  `IsTildeModelOnAnyModel.isTildeModelOn` are the two halves named separately.
* `isTildeModelOn_charts_of_hasUpperShriekCharts` and
  `hasUpperShriekCharts_of_isTildeModelOn_charts` — the chart description
  `Stacks.Duality.HasUpperShriekCharts`, read at the standard model, is exactly the chart
  hypothesis phrased with `Stacks.Duality.IsTildeModelOn`.
* `isDualizingComplex_fShriek_of_hasUpperShriekCharts` — the conditional form of
  [Stacks, Tag 0AA3] with its one remaining hypothesis asked for in the shape the chart
  description is proved in.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)

## Implementation notes

No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes. Both
predicates are repository bookkeeping, not statements of the Stacks Project; a comparison between
two spellings of one notion carries no tag.

The file pins `CategoryTheory.HasDerivedCategory.standard` by writing it into each statement with
`@`, rather than by a local instance attribute. Writing it out is what makes the comparison
visible: the whole point of these lemmas is *which* model each side is read at, and an attribute
would hide that in the file header. It has to be written into
`Stacks.Duality.IsDualizingComplex` too: the objects of the two models of `D(𝒪_X)` are literally
the same, so a predicate on them left to instance resolution would silently be read at the
locally small model instead, and the resulting statement would be about a different predicate on
the same complex.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

section TildeModel

variable {X : Scheme.{u}}

/-- **The two affine modelling predicates are the same function.**
`Stacks.Duality.IsTildeModelOnAnyModel`, whose model of `D(𝒪_X)` is a binder, instantiated at
`CategoryTheory.HasDerivedCategory.standard`, is `Stacks.Duality.IsTildeModelOn`, whose model is
that one. The inner model, of `D(Γ(X, U))`, is the standard one on both sides already.

Stated as an equality of functions so that it can rewrite an occurrence of either predicate
underneath the quantifiers of a chart description. -/
theorem isTildeModelOnAnyModel_standard_eq (X : Scheme.{u}) :
    @IsTildeModelOnAnyModel X (HasDerivedCategory.standard _) = @IsTildeModelOn X :=
  rfl

/-- The comparison of `isTildeModelOnAnyModel_standard_eq` at a point, as an `Iff`: at the
standard model, being modelled by `ω` on `U` in the sense with a free model binder and in the
sense with the model pinned are the same statement. Both directions hold. -/
theorem isTildeModelOnAnyModel_standard_iff
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (U : X.Opens) (hU : IsAffineOpen U)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _)) :
    @IsTildeModelOnAnyModel X (HasDerivedCategory.standard _) K U hU ω ↔
      IsTildeModelOn K U hU ω :=
  Iff.rfl

/-- A model in the pinned sense is a model in the sense with a free model binder, read at the
standard model. -/
theorem IsTildeModelOn.isTildeModelOnAnyModel
    {K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {U : X.Opens} {hU : IsAffineOpen U}
    {ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _)}
    (h : IsTildeModelOn K U hU ω) :
    @IsTildeModelOnAnyModel X (HasDerivedCategory.standard _) K U hU ω :=
  h

/-- A model in the sense with a free model binder, read at the standard model, is a model in the
pinned sense. -/
theorem IsTildeModelOnAnyModel.isTildeModelOn
    {K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    {U : X.Opens} {hU : IsAffineOpen U}
    {ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _)}
    (h : @IsTildeModelOnAnyModel X (HasDerivedCategory.standard _) K U hU ω) :
    IsTildeModelOn K U hU ω :=
  h

end TildeModel

section Charts

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **The chart description, read at the standard model, is the chart hypothesis in the pinned
modelling predicate.** Over affine opens `U ⊆ f⁻¹(V)` and a model `ω` of `K` on `V`, some
polynomial presentation of `Γ(Y, V) → Γ(X, U)` carries `ω` to a model of `L` on `U`.

The hypothesis is `Stacks.Duality.HasUpperShriekCharts`, the shape in which the affine chart
description of `f^!` is proved; the conclusion is the shape in which a statement that pins
`CategoryTheory.HasDerivedCategory.standard` asks for it. The existential over presentations is
already in `HasUpperShriekCharts`, so nothing is chosen here. -/
theorem isTildeModelOn_charts_of_hasUpperShriekCharts (f : X ⟶ Y)
    {K : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    {L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    (h : @HasUpperShriekCharts X Y _ _ f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) K L) :
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V)
      (ω : @DerivedCategory (ModuleCat.{u} Γ(Y, V)) _ _ (HasDerivedCategory.standard _)),
      IsTildeModelOn K V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.appLE V U hUV).hom,
        IsTildeModelOn L U hU (p.upperShriekFunctor.{u, u}.obj ω) :=
  h

/-- The converse of `Stacks.Duality.isTildeModelOn_charts_of_hasUpperShriekCharts`: the chart
hypothesis phrased with the pinned modelling predicate is the chart description
`Stacks.Duality.HasUpperShriekCharts` read at the standard model. -/
theorem hasUpperShriekCharts_of_isTildeModelOn_charts (f : X ⟶ Y)
    {K : @DerivedCategory Y.Modules _ _ (HasDerivedCategory.standard _)}
    {L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)}
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V)
      (ω : @DerivedCategory (ModuleCat.{u} Γ(Y, V)) _ _ (HasDerivedCategory.standard _)),
      IsTildeModelOn K V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.appLE V U hUV).hom,
        IsTildeModelOn L U hU (p.upperShriekFunctor.{u, u}.obj ω)) :
    @HasUpperShriekCharts X Y _ _ f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) K L :=
  h

end Charts

section Dualizing

/-- **The chart hypothesis of `Stacks.Duality.isDualizingComplex_upperShriek_of_fts_of_chart`,
asked for in the shape the chart description is proved in.** Let `S` be Noetherian, `f : X ⟶ Y` a
morphism of `AlgebraicGeometry.FTS S`, `fShriek` a candidate `f^!` on `D⁺_QCoh` and `K` a
dualizing complex on `Y`. If `fShriek K` has the affine chart description
`Stacks.Duality.HasUpperShriekCharts` of `K` along `f`, read at the standard model, then
`fShriek K` is a dualizing complex.

This is that statement with its chart hypothesis rewritten by
`Stacks.Duality.isTildeModelOn_charts_of_hasUpperShriekCharts`, which is an identity of
statements; the cover criterion was already discharged in the input. So what the conditional form
of [Stacks, Tag 0AA3] still carries is precisely the affine chart description of clause (b) of
[Stacks, Remark 0BV2] *at the standard model* — the hypothesis is no longer phrased in a
predicate different from the one in which that description is stated and proved.

No `@[stacks]` attribute is placed here: the statement still carries `hchart`, and rewriting a
hypothesis into an equal one neither registers nor discharges anything. -/
theorem isDualizingComplex_fShriek_of_hasUpperShriekCharts {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y)
    (fShriek : quasiCoherentDerivedCategoryPlus Y.left ⥤ quasiCoherentDerivedCategoryPlus X.left)
    (K : quasiCoherentDerivedCategoryPlus Y.left)
    (hchart : @HasUpperShriekCharts X.left Y.left _ _ f.left
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      K.obj.obj (fShriek.obj K).obj.obj)
    (hK : @IsDualizingComplex Y.left _ (HasDerivedCategory.standard _) K.obj.obj) :
    @IsDualizingComplex X.left _ (HasDerivedCategory.standard _) (fShriek.obj K).obj.obj :=
  isDualizingComplex_upperShriek_of_fts_of_chart f fShriek K
    (isTildeModelOn_charts_of_hasUpperShriekCharts f.left hchart) hK

end Dualizing

end Stacks.Duality

end
