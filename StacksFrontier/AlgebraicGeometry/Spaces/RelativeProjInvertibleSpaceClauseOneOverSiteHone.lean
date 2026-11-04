module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneOverSiteSquareOnly
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePointSiteCross
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaChartMaps

/-!
# Clause (1) of Stacks 0D2Z at the scheme points of `U(ψ)`, with no hypothesis

Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` (the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`) is the point identity
`…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'` at the target square over the
site of `s.shrink`, which is the target square over the site of `s`
(`…InvertibleTwistingRestriction.targetSquareOverSite_square`) carried across
`s.shrink.site = s.site` by `…InvertibleTwistingRestriction.targetSquare_of_site_heq`, its leaves
compared one by one.

## Main results

* `…InvertibleTwistingRestriction.modulePullback_map_clauseOneProjLeg_comp_chartMap`: **clause (1)
  of Stacks 0D2Z at a scheme point of `U(ψ)`**, with no hypothesis.
* `…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_chartMaps`: `θ` with clause
  (1), with no hypothesis.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

set_option maxHeartbeats 0 in
-- Unifying the long chain of `HEq.rfl` site transports between `s` and `s.shrink` needs deep
-- definitional unfolding, beyond the default heartbeat bound.
/-- **Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`**: the inverse image along
`w` of the `ψ_P` leg followed by the chart map `χ_w` is the inverse image along `w` of the `ψ` leg
(the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`), with no hypothesis:
`…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'` at the target square over the site
of `s` (`…InvertibleTwistingRestriction.targetSquareOverSite_square`), carried to the site of
`s.shrink` by `…InvertibleTwistingRestriction.targetSquare_of_site_heq`. -/
theorem modulePullback_map_clauseOneProjLeg_comp_chartMap :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOnePsiLeg s f L ψ d) :=
  clauseOnePoint_of_targetSquare' Px w d
    (targetSquare_of_site_heq s.shrink_site.symm s.shrink_base.symm
      (targetSquareOverSite_square w d) HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl
      (modulePullbackCompTransportIso_hom_heq_of_site s.shrink_site.symm s.shrink_base.symm
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      HEq.rfl HEq.rfl HEq.rfl
      (quasicoherentHomMk_heq_of_site s.shrink_site.symm s.shrink_base.symm HEq.rfl HEq.rfl HEq.rfl
        (pointPsi_app_heq_of_site (B₁ := s.site) (B₂ := s.shrink.site) (S₁ := s.base)
          (S₂ := s.shrink.base) (hS₁ := s.containsBase) (hS₂ := s.shrink.containsBase)
          s.shrink_site.symm s.shrink_base.symm (X₁ := X) (Y₁ := s.space) (f₁ := f)
          (A₁ := s.shrink.algebra) (L₁ := L) (hL₁ := hL) (ψ₁ := ψ) (T₁ := W)
          (x₁ := locusPoint w) (X₂ := X) (Y₂ := s.shrink.space) (f₂ := f)
          (A₂ := s.shrink.algebra) (L₂ := L) (hL₂ := hL) (ψ₂ := ψ) (T₂ := W)
          (x₂ := locusPoint w) HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
          (d : ℤ)))
      HEq.rfl HEq.rfl)

/-- **`θ` of [Stacks, Tag 0D2Z] with clause (1)** for a pair `(ℒ, ψ)` on the algebraic space `X`,
with no hypothesis: `…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points` with
clause (1) at the scheme points supplied by
`…InvertibleTwistingRestriction.modulePullback_map_clauseOneProjLeg_comp_chartMap`. -/
theorem exists_theta_clauseOneSections_of_chartMaps :
    type_of% (exists_theta_clauseOneSections_of_points (s := s) (f := f) (L := L) (ψ := ψ)
      (fun Px d _ w => modulePullback_map_clauseOneProjLeg_comp_chartMap Px w d)) :=
  exists_theta_clauseOneSections_of_points (s := s) (f := f) (L := L) (ψ := ψ)
    (fun Px d _ w => modulePullback_map_clauseOneProjLeg_comp_chartMap Px w d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
