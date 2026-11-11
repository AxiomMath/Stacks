module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts

/-!
# The exceptional inverse image of a dualizing complex is dualizing

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a morphism of `FTS S` ([Stacks, Tag 0F42]) with
a compactification `j`. If `K` is a dualizing complex on `Y`, then `f^!K` is a dualizing complex
on `X`: this is [Stacks, Tag 0AA3]. The proof is the source's: on affine charts `f^!K` is the
associated sheaf of the algebraic upper shriek of a model of `K` ([Stacks, Tag 0BV2],
`Stacks.Duality.UpperShriekCharts`), the algebraic upper shriek of a dualizing complex is
dualizing ([Stacks, Tag 0BZL]), and being dualizing is local ([Stacks, Tag 0A86]).

## Main results

* `Stacks.Duality.UpperShriekCharts.hasUpperShriekCharts` — the chart description of `f^!K` in
  the shape `Stacks.Duality.HasUpperShriekCharts` consumed by the dualizing criterion.
* `Stacks.Duality.isDualizingComplex_upperShriek_obj` — [Stacks, Tag 0AA3].

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open ChartCompactification Stacks.Duality.ProjectiveSpace AlgebraicGeometry.ProjectiveSpace
  Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- The chart description `Stacks.Duality.UpperShriekCharts` of `f^!E`, read with the model of
`D(𝒪_U)` of `Stacks.Duality.IsTildeModelOnAnyModel` and with some presentation of each chart ring
map. -/
theorem UpperShriekCharts.hasUpperShriekCharts {E : quasiCoherentDerivedCategory Y.left}
    (h : UpperShriekCharts f j E) :
    HasUpperShriekCharts f.left E.obj ((upperShriek f j).obj E).obj := by
  intro U hU V hV hUV ω hω
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _ (f.left.finiteType_appLE hV hU hUV)
  obtain ⟨e⟩ := h V hV U hU hUV p ω hω
  exact ⟨p, ⟨Stacks.Injectives.isoOfTargetModelIso.{u} U.toScheme.Modules
    (Scheme.Modules.restrictFunctor U.ι)
    (hd₂ := HasDerivedCategory.standard (ModuleCat.{u} Γ(X.left, U)))
    (tilde.functor Γ(X.left, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ e⟩⟩

/-- **Stacks Project, Tag 0AA3 (Lemma 48.17.7).** In Situation 48.16.1 let `f : X ⟶ Y` be a
morphism of `FTS S`. If `K` is a dualizing complex for `Y`, then `f^!K` is a dualizing complex for
`X`. Here `f^!` is computed at an arbitrary compactification `j`. -/
@[stacks 0AA3 "f^! is the library's upper shriek functor of Tag 0A9Y at an arbitrary \
  compactification j of f; the only hypothesis is that K is a dualizing complex on Y"]
theorem isDualizingComplex_upperShriek_obj
    (K : quasiCoherentDerivedCategory Y.left) (hK : IsDualizingComplex K.obj) :
    IsDualizingComplex ((upperShriek f j).obj K).obj :=
  isDualizingComplex_of_isTildeModelOn_upperShriekFunctor f.left K.obj _
    (UpperShriekCharts.hasUpperShriekCharts f j
      (upperShriekCharts f j K (isBoundedBelow_of_isDualizingComplex _ hK))) hK

/-- A morphism `f : X ⟶ S` of finite type and separated, as a morphism of `FTS S` from `X` to the
terminal object `S`. -/
abbrev ftsHomToBase {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : FTS.mk f ⟶ FTS.mk (𝟙 S) :=
  MorphismProperty.Over.homMk f (Category.comp_id f) trivial

end Stacks.Duality

end
