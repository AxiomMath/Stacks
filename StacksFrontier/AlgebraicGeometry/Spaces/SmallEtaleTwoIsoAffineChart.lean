module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection

/-!
# Projection compatibility over an affine chart

Over an *affine* étale scheme chart `V` of `Y`, the agreement on regular functions produced by
`AlgebraicGeometry.Space.exists_smallBaseChange_iso_gamma_projection` upgrades to an equality of
morphisms of schemes: a morphism into an affine scheme is determined by the induced map on
global regular functions.

## Main results

* `AlgebraicGeometry.hom_ext_of_isAffine_target`: two morphisms of schemes into an affine scheme
  which induce the same map on global sections are equal.
* `AlgebraicGeometry.Space.exists_smallBaseChange_iso_projection_affine`: from a 2-isomorphism of
  the morphisms of small étale ringed topoi of two representable morphisms `a, b : X ⟶ Y`, an
  isomorphism `e` of the chart base-change functors which is compatible with the two cartesian
  projections over every affine étale scheme chart of `Y`.

## Implementation notes

The affine step is the unit of the `Γ ⊣ Spec` adjunction: naturality of
`AlgebraicGeometry.Scheme.toSpecΓ` turns an equality of the maps on global sections into an
equality after composing with `V.toSpecΓ`, which is an isomorphism exactly because `V` is
affine (`AlgebraicGeometry.IsAffine`).

The chart statement keeps the whole natural isomorphism `e`, not just its component at one
chart: the passage from the affine charts to a *surjective* chart — which is what
`AlgebraicGeometry.Space.eq_of_chartHom_projection` consumes — goes through naturality of `e`
along the inclusions of the affine charts into a surjective one.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Two morphisms of schemes into an affine scheme which agree on global regular functions are
equal.** -/
theorem hom_ext_of_isAffine_target {W V : Scheme.{u}} [IsAffine V] (g₁ g₂ : W ⟶ V)
    (h : Scheme.Γ.map g₁.op = Scheme.Γ.map g₂.op) : g₁ = g₂ := by
  have : IsIso V.toSpecΓ := IsAffine.affine
  have hc : g₁ ≫ V.toSpecΓ = g₂ ≫ V.toSpecΓ := by
    rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, ← Scheme.Γ_map_op,
      ← Scheme.Γ_map_op, h]
  exact (cancel_mono V.toSpecΓ).mp hc

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Projection compatibility over an affine chart.** From a 2-isomorphism of the morphisms of
small étale ringed topoi of two representable morphisms `a, b : X ⟶ Y`, an isomorphism of the
chart base-change functors whose component at any *affine* étale scheme chart `V` of `Y`
commutes with the two cartesian projections to `V`. -/
theorem exists_smallBaseChange_iso_projection_affine (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS a) (smallEtaleRingedToposHom B S hS b)) :
    letI := isContinuous_smallBaseChange B S hS a ha
    letI := isContinuous_smallBaseChange B S hS b hb
    ∃ e : smallBaseChange B S hS b hb ≅ smallBaseChange B S hS a ha,
      ∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
        (e.hom.app V).hom.left ≫ ha.snd V.1.hom = hb.snd V.1.hom := by
  let := isContinuous_smallBaseChange B S hS a ha
  let := isContinuous_smallBaseChange B S hS b hb
  obtain ⟨e, he⟩ := exists_smallBaseChange_iso_gamma_projection B S hS a b ha hb t
  refine ⟨e, fun V hV => ?_⟩
  have := hV
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine hom_ext_of_isAffine_target _ _ ?_
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  exact he V s

end Space

end AlgebraicGeometry

end
