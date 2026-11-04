module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetUnitSlots

/-!
# The slot `hsite` of the target square of clause (1) of Stacks 0D2Z at a scheme point

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso`) takes as its hypothesis `hsite` the naturality square of the
identification `ρ_r` along `r = c ≫ q`, for the section `c` of the structure morphism
`q : W ×_Y P ⟶ W`.  At `r = 𝟙` (`c ≫ q = 𝟙`), with `ρ_r` the unit law `(𝟙)^* ≅ 𝟭` of Stacks
03LU and `F_c = 𝟙`, this is
`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom` at variables.
This file instantiates it at the chart data, over the site of `s.shrink`: the point
`f ∘ x : W ⟶ Y` of the base under `w`, the piece `𝒜_d`, and the identification `ζ` of
`(f ∘ x)^*𝒜_d` with the module attached to its Zariski reading, spelled as in the hypothesis
`hTZ` (`…InvertibleTwistingRestriction.compIso_hom_app_comp_map_pointPsi_app_locusPoint`). The
statement is the instance's own type (`type_of%`), so no factor is re-elaborated.

## Main results

* `…InvertibleTwistingRestriction.targetSquare_hsite`: **the hypothesis `hsite` of the target
  square at a scheme point `w` of `U(ψ)`**, at `r = 𝟙`.

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

/-- **The hypothesis `hsite` of the target square of clause (1) at a scheme point `w` of `U(ψ)`**,
at `r = 𝟙`: the inverse image along `𝟙` of the identification `ζ` of `(f ∘ x)^*𝒜_d` with the
module attached to its Zariski reading, followed by the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU and
`F_c = 𝟙`, is the comparison `(𝟙)^*(f ∘ x)^* ≅ (𝟙 ≫ (f ∘ x))^*` at `𝒜_d`, the transport along
`𝟙 ≫ (f ∘ x) = f ∘ x` and `ζ`.  This is the hypothesis `hsite` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over the site of `s.shrink`, with `ζ` spelled as in the hypothesis
`hTZ`. -/
theorem targetSquare_hsite :
    type_of% (modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom
      (pointHom (locusPoint w ≫ f.hom)) (s.shrink.algebra.piece (d : ℤ))
      (zariskiReadingQuasicoherentIso W _
        (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))) :=
  modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom
    (pointHom (locusPoint w ≫ f.hom)) (s.shrink.algebra.piece (d : ℤ))
    (zariskiReadingQuasicoherentIso W _
      (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
        (locusPoint w ≫ f.hom) (d : ℤ)))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
