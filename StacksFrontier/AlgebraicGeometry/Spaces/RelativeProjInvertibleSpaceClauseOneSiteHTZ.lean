module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePointPsiSquare

/-!
# The square of `ψ` at a scheme point of `U(ψ)`, over the site of `s`

The square of `ψ_d` at the scheme point `x : W ⟶ X` underlying a scheme point `w : W ⟶ U(ψ)`,
that is, `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app` over the
site `s.site` of `s` (not over the site of `s.shrink`), at the base space `s.space`, the algebra
`s.shrink.algebra` and the pair `(ℒ, ψ)` of `U(ψ)`. The identification `ζ` of `(f ∘ x)^*𝒜_d` with
the module attached to its Zariski reading is then spelled as the fourth factor of
`…RelativeProjSituation.fibrePsiSourceIso`.

## Main results

* `…InvertibleTwistingRestriction.targetSquareSite_hTZ`: the square of `ψ_d` at the scheme point
  of `X` underlying a scheme point `w` of `U(ψ)`, over the site of `s`.

## Implementation notes

The statement is the type (`type_of%`) of the instance of
`AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app`, so no factor is
re-elaborated and no two spellings of the site are compared.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
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
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- The square of `ψ_d` at the scheme point `x : W ⟶ X` underlying a scheme point `w` of `U(ψ)`,
over the site of `s`: the comparison `x^*(f^*𝒜_d) ≅ (x ≫ f)^*𝒜_d` of Stacks 03LU, the transport
along `x ≫ f = f ∘ x`, the identification `ζ` of `(f ∘ x)^*𝒜_d` with the module attached to its
Zariski reading (the fourth factor of `…RelativeProjSituation.fibrePsiSourceIso`) and the module
attached to `x^*ψ` in degree `d` are the inverse image along `x` of `ψ_d` followed by
`AlgebraicGeometry.Space.pointTargetIso`. -/
theorem targetSquareSite_hTZ :
    type_of% (compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app
      (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (Y := s.space) (hL := hL)
      f s.shrink.algebra L ψ W (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
      (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)) :=
  compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app
    (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (Y := s.space) (hL := hL)
    f s.shrink.algebra L ψ W (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
    (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
