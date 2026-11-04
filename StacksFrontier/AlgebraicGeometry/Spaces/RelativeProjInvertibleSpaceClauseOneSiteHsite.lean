module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOne
public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetUnitSlots

/-!
# The unit-law naturality square at a scheme point of `U(ψ)`, over the site of `s`

Let `w : W ⟶ U(ψ)` be a scheme point, `x : W ⟶ X` the scheme point underlying it and
`f ∘ x : W ⟶ Y` the point of the base under it. The inverse image along `𝟙` of the identification
`ζ` of `(f ∘ x)^*𝒜_d` with the module attached to its Zariski reading, followed by the unit law
`(𝟙)^* ≅ 𝟭` of Stacks 03LU, is the comparison `(𝟙)^*(f ∘ x)^* ≅ (𝟙 ≫ (f ∘ x))^*` at `𝒜_d`, the
transport along `𝟙 ≫ (f ∘ x) = f ∘ x` and `ζ`. This is
`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom` over the site
`s.site` of `s` (not over the site of `s.shrink`), with `ζ` spelled as the fourth factor of
`…RelativeProjSituation.fibrePsiSourceIso` (over `s.site`, with the base space `s.space`).

## Main results

* `…InvertibleTwistingRestriction.targetSquareSite_hsite`: the unit-law naturality square at a
  scheme point `w` of `U(ψ)`, over the site of `s`.

## Implementation notes

The point, the piece and `ζ` are formed at variables (the site, the spaces, `f`, `𝒜`, the scheme
point) and the variables are then set to the chart data, so that every factor is spelled over
`s.site` exactly as in `…InvertibleTwistingRestriction.targetSquareSite_hTZ`. The statement is the
type of that instance (`type_of%`), so no factor is re-elaborated and no two spellings of the site
are compared.

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

/-- The unit-law naturality square at a scheme point `w` of `U(ψ)`, over the site of `s`: the
inverse image along `𝟙` of the identification `ζ` of `(f ∘ x)^*𝒜_d` with the module attached to
its Zariski reading (the fourth factor of `…RelativeProjSituation.fibrePsiSourceIso`), followed by
the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU, is the comparison `(𝟙)^*(f ∘ x)^* ≅ (𝟙 ≫ (f ∘ x))^*` at
`𝒜_d`, the transport along `𝟙 ≫ (f ∘ x) = f ∘ x` and `ζ`. -/
theorem targetSquareSite_hsite :
    type_of% ((fun (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
        (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
        (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite) (T : BigFppfOver B S hS)
        (x : yoneda.obj T ⟶ X.1) (n : ℤ) =>
      modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom (pointHom (x ≫ f.hom)) (A.piece n)
        (zariskiReadingQuasicoherentIso T _
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)))
      s.site s.base s.containsBase X s.space f s.shrink.algebra s.shrink.isQuasicoherent W
      (locusPoint w) (d : ℤ)) :=
  (fun (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
      (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
      (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite) (T : BigFppfOver B S hS)
      (x : yoneda.obj T ⟶ X.1) (n : ℤ) =>
    modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom (pointHom (x ≫ f.hom)) (A.piece n)
      (zariskiReadingQuasicoherentIso T _
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)))
    s.site s.base s.containsBase X s.space f s.shrink.algebra s.shrink.isQuasicoherent W
    (locusPoint w) (d : ℤ)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
