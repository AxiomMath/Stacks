module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono

/-!
# Permanence of the finiteness conditions along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over `S`. Composing an étale chart
of `X` with `f` is an étale chart of `Y`, so each finiteness condition on the charts of `Y`
above a point `y` restricts to a finiteness condition on the charts of `X` above every point
lying over `y`. This file carries out that restriction for condition (1) of Stacks 03JV, the
finiteness of both the chart fibre and the relation fibre, which is condition `(γ)` of
Stacks 03JX.

## Main results

* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAt_of_isEtale` transfers
  condition (1) of Stacks 03JV from a point of the target to each point of the source.
* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isEtale` is the
  same statement for condition `(γ)` of Stacks 03JX.

## Implementation notes

The relation fibre is handled by the monomorphism from the self-intersection of a chart of
`X` to the self-intersection of the corresponding chart of `Y`, which is injective on points
by Stacks 06RV; the chart fibre is handled by a plain inclusion of preimages. Neither space
is required to be an algebraic space: only the behaviour of étale charts under composition
with `f` is used, so the statements hold for arbitrary presheaves on the big fppf site.

This is the content of Stacks 0ABU for condition `(γ)`. The source states 0ABU for a
*decent* source and target, and `AlgebraicGeometry.Space.IsDecentSpace` spells decency with
condition (4) of Stacks 03JV, a quasi-compact monomorphism from the spectrum of a field.
Deducing that form from the one proved here is the equivalence of conditions (1) and (4) of
Stacks 03JV, which is now available as
`hasFiniteChartAndRelationFibersAt_iff_hasQuasiCompactMonomorphicFieldRepresentative`
in `StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint`, and the
resulting statement is `AlgebraicGeometry.Space.isDecentSpace_of_isEtale` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency`, which carries
`@[stacks 0ABU "decent"]`. These declarations are the chart-level half of that argument and so
do not carry the tag themselves.

The *reasonable* half of Stacks 0ABU makes the same comparison on degrees rather than on point
sets: the fibre of a chart over the source is an open subscheme of its fibre over the target,
the diagonal of an étale morphism being an open immersion, and an open subscheme of a scheme
finite locally free of rank `r` over a field has rank at most `r`. It is
`AlgebraicGeometry.Space.isReasonableSpace_of_isEtale` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceReasonableness`.

## References

* [Stacks Project, Tag 0ABU](https://stacks.math.columbia.edu/tag/0ABU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Condition (1) of Stacks 03JV passes from a point of the target of an étale morphism to
every point of the source above it: the étale charts of the source are étale charts of the
target after composing with the morphism, and their self-intersections map monomorphically. -/
theorem hasFiniteChartAndRelationFibersAt_of_isEtale (f : X ⟶ Y) (hf : IsEtale B S hS f)
    (x : points B S hS X)
    (hy : HasFiniteChartAndRelationFibersAt B S hS Y (pointsMap B S hS X f x)) :
    HasFiniteChartAndRelationFibersAt B S hS X x := by
  intro U hU φ hφ
  let y := pointsMap B S hS X f x
  let ψ : yoneda.obj U ⟶ Y := φ ≫ f
  have hfinite := hy U hU ψ (hf U φ hφ)
  refine ⟨?_, ?_⟩
  · refine hfinite.1.subset fun z hz => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
    rw [show ψ = φ ≫ f from rfl, pointsMap_comp_apply, hz]
  · let R := pullback φ φ
    let RY := pullback ψ ψ
    let ρ : R ⟶ RY := pullback.lift (pullback.fst φ φ) (pullback.snd φ φ) (by
      dsimp [ψ]
      exact congrArg (fun q => q ≫ f) pullback.condition)
    have : Mono ρ := ⟨fun a b hab => pullback.hom_ext
      (by simpa only [Category.assoc, ρ, pullback.lift_fst] using
        congrArg (fun t => t ≫ pullback.fst ψ ψ) hab)
      (by simpa only [Category.assoc, ρ, pullback.lift_snd] using
        congrArg (fun t => t ≫ pullback.snd ψ ψ) hab)⟩
    let θ := pullback.fst φ φ ≫ φ
    let θY := pullback.fst ψ ψ ≫ ψ
    have hρθ : ρ ≫ θY = θ ≫ f := by
      dsimp only [ρ, θ, θY]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc]
    let sourceFiber := pointsMap B S hS R θ ⁻¹' {x}
    let targetFiber := pointsMap B S hS RY θY ⁻¹' {y}
    have : Finite ↑targetFiber := hfinite.2.to_subtype
    let fiberMap : sourceFiber → targetFiber := fun z =>
      ⟨pointsMap B S hS R ρ z.1, by
        change pointsMap B S hS RY θY (pointsMap B S hS R ρ z.1) = y
        rw [← pointsMap_comp_apply, hρθ, pointsMap_comp_apply]
        exact congrArg (pointsMap B S hS X f) z.2⟩
    exact Set.finite_coe_iff.mp <| Finite.of_injective fiberMap fun a b h => Subtype.ext
      ((pointsMap_injective_of_mono B S hS ρ) (congrArg Subtype.val h))

/-- **Condition `(γ)` of Stacks 03JX ascends along an étale morphism.** If every point of
the target of an étale morphism satisfies condition (1) of Stacks 03JV, then so does every
point of the source. -/
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_isEtale (f : X ⟶ Y)
    (hf : IsEtale B S hS f)
    (hY : HasFiniteChartAndRelationFibersAtEveryPoint B S hS Y) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X :=
  fun x => hasFiniteChartAndRelationFibersAt_of_isEtale B S hS f hf x (hY _)

end AlgebraicGeometry.Space

end
