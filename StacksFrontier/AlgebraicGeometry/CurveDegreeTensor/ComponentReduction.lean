module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Formula
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic

/-!
# [Stacks, Tag 0AYX] on a proper scheme of dimension at most one, from [Stacks, Tag 0AYW]

[Stacks, Tag 0AYX] states that for `ℰ` and `𝒱` locally free of constant finite ranks `n` and `m`
on a scheme `X` proper of dimension at most one over a field `k`,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add`
(`StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Cohomological.lean`) proves it with no
hypothesis when `X` is a proper *curve*. The source's remaining step is the sentence "by
Lemma 0AYW and elementary arithmetic, we reduce to the case of a proper curve", and this file is
that sentence: the component formula of [Stacks, Tag 0AYW],

`deg(𝒲) = ∑ᶠ ξ, m(ξ) · deg(𝒲|_{C(ξ)})`,

applied to the three modules `ℰ`, `𝒱` and `ℰ ⊗ 𝒱`, turns the statement on `X` into the statement
on each reduced one-dimensional component, and each such component *is* a proper curve over `k`
by `Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `componentDegree_tensorSheaf_eq_add`: **the component-local case, with no hypothesis.** On the
  reduced one-dimensional component indexed by `ξ`,
  `deg((ℰ ⊗ 𝒱)|_{C(ξ)}) = m · deg(ℰ|_{C(ξ)}) + n · deg(𝒱|_{C(ξ)})`.
* `curveDegree_tensorSheaf_eq_add_of_componentFormula`: **[Stacks, Tag 0AYX] on a proper scheme
  of dimension at most one**, from the conclusion of [Stacks, Tag 0AYW] as the single hypothesis
  `h0AYW`.

## Implementation notes

**No `@[stacks 0AYX]` attribute is attached here.** The tag itself is proved unconditionally, as
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one` in
`StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Devissage.lean`, by a dévissage on `X` that does
not pass through [Stacks, Tag 0AYW] at all. What this file records is the source's own route, and
what keeps the attribute off it is `h0AYW`: a hypothesis the tag does not have. Its content is
exactly the conclusion of [Stacks, Tag 0AYW], quantified
over the finite locally free modules of constant rank on the one scheme `X` — the quantifier is
needed because the reduction uses the formula three times, at `ℰ`, at `𝒱` and at `ℰ ⊗ 𝒱`, and
those are three different modules of three different ranks. Each of the four forms of
[Stacks, Tag 0AYW] in
`StacksFrontier/AlgebraicGeometry/ComponentMultiplicity/Devissage.lean` still carries the two steps
of the source argument as hypotheses of its own, so none of them discharges `h0AYW`.

**The component-local case needs no hypothesis**, which is the point of
`componentDegree_tensorSheaf_eq_add` being stated separately: the reduced component carries an
`AlgebraicGeometry.IsCurve` instance, so the hypothesis-free curve form of Tag 0AYX applies to
it directly, and the restriction of a tensor product is the tensor product of the restrictions by
[Stacks, Tag 01CD] (`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso`).

**Why the degrees are rebound rather than rewritten.**
`AlgebraicGeometry.curveDegree` takes the rank, the dimension bound and the local freeness as
arguments, and `Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree` is by definition that
degree on the component with all three supplied in one particular spelling. The three are
propositions, so any two proofs of them are interchangeable; the statements below are therefore
written at `componentDegree` and converted by `show`, rather than by rewriting under a motive
that would have to match the spellings syntactically.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

/-- **The component-local case of [Stacks, Tag 0AYX], with no hypothesis.** For `ℰ` and `𝒱`
finite locally free of constant ranks `n` and `m` on a scheme `X` proper of dimension at most one
over a field, and `ξ` the generic point of a one-dimensional irreducible component,

`deg((ℰ ⊗ 𝒱)|_{C(ξ)}) = m · deg(ℰ|_{C(ξ)}) + n · deg(𝒱|_{C(ξ)})`.

The reduced component `C(ξ)` is a proper curve over the field
(`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`), so
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add` applies to it; the restriction of the tensor
product is identified with the tensor product of the restrictions by [Stacks, Tag 01CD], and
`AlgebraicGeometry.curveDegree_eq_of_iso` moves the degree across that identification. -/
public theorem componentDegree_tensorSheaf_eq_add (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    (ξ : genericPointsOne X) :
    @componentDegree k _ X f _ hdim
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj V) (n * m)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) ξ =
      (m : ℤ) * componentDegree k f hdim E n ξ + (n : ℤ) * componentDegree k f hdim V m ξ := by
  have hproper : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  have hiscurve : IsCurve k (reducedComponentι X ξ ≫ f) := isCurve_reducedComponentι_comp k f ξ
  have hdimC : topologicalKrullDim (reducedComponent X ξ) ≤ 1 :=
    topologicalKrullDim_reducedComponent_le X hdim ξ
  have hE' := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ E n
  have hV' := isFiniteLocallyFreeOfRank_pullback_reducedComponentι ξ V m
  have hT' := @isFiniteLocallyFreeOfRank_pullback_reducedComponentι X ξ
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj V) (n * m)
    (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m)
  -- [Stacks, Tag 01CD]: the restriction of the tensor product is the tensor product of the
  -- restrictions, and the degree does not see the identification.
  have hiso := @curveDegree_eq_of_iso k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
    hproper hdimC
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj V))
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(reducedComponent X ξ).toRingedSpace.presheaf,
        (reducedComponent X ξ).toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)).obj
        ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj V)) (n * m) hT'
    (@SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf (reducedComponent X ξ) _ _ n m hE' hV')
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (reducedComponentι X ξ) E V)
  -- [Stacks, Tag 0AYX] on the component, which is a proper curve.
  have hcurve := @curveDegree_tensorSheaf_eq_add k _ (reducedComponent X ξ)
    (reducedComponentι X ξ ≫ f) hiscurve hproper hdimC
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E)
    ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj V) n m hE' hV'
  show @curveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f) hproper hdimC
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj V))
      (n * m) hT' = _
  -- The two remaining degrees are the two `componentDegree`s by definition, their local-freeness
  -- and dimension proofs being interchangeable with the ones below.
  rw [hiso, hcurve]
  rfl

/-- **[Stacks, Tag 0AYX] on a proper scheme of dimension at most one.** For `ℰ` and `𝒱` finite
locally free of constant ranks `n` and `m` on a scheme `X` proper of dimension at most one over a
field `k`,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

The single hypothesis `h0AYW` is the conclusion of [Stacks, Tag 0AYW] for the finite locally free
modules of constant rank on `X`: the degree is the multiplicity-weighted sum of the degrees on
the reduced one-dimensional components. Given it, the identity is the source's "elementary
arithmetic": the formula is applied at `ℰ ⊗ 𝒱`, at `ℰ` and at `𝒱`, the three sums are compared
term by term through `AlgebraicGeometry.componentDegree_tensorSheaf_eq_add`, and the components
are finite in number because `X` is Noetherian
(`Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne_of_isProper`).

See the module docstring for why the tag is not attached here. -/
public theorem curveDegree_tensorSheaf_eq_add_of_componentFormula (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (h0AYW : ∀ (W : X.Modules) (r : ℕ)
      (hW : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} W r),
      @curveDegree k _ X f _ hdim W r hW =
        ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) *
          @componentDegree k _ X f _ hdim W r hW ξ)
    (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m] :
    @curveDegree k _ X f _ hdim
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj V) (n * m)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m := by
  classical
  have hfinite : Finite (genericPointsOne X) :=
    (finite_genericPointsOne_of_isProper k f).to_subtype
  let _ : Fintype (genericPointsOne X) := Fintype.ofFinite _
  rw [h0AYW _ (n * m) (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m),
    h0AYW E n ‹_›, h0AYW V m ‹_›, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [componentDegree_tensorSheaf_eq_add k f hdim E V n m ξ]
  ring

end AlgebraicGeometry

end
