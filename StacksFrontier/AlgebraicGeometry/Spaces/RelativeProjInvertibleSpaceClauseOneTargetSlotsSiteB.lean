module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetSquare

/-!
# The slot `hΓ` of the target square of clause (1) of Stacks 0D2Z, over the site of `s`

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) takes as its hypothesis `hΓ` the
scheme-level identity `F_q ≫ F_c = FG₁`.  At `r = 𝟙` (the section `c_w` of the structure morphism
`q : W ×_Y P ⟶ W`, with `c_w ≫ q = 𝟙`), `F_q = FG₁` is the module attached (Stacks 03DX (2)) to the
canonical identification `c_w^*q^*Z ≅ (c_w ≫ q)^*Z = (𝟙)^*Z ≅ Z` of the restriction
`Z = (f ∘ x)^*𝒜_d` of the piece `𝒜_d` to the point `f ∘ x` of the base under `w`
(`…pointPieceQcoh`), and `F_c = 𝟙`, so the slot is `Category.comp_id`.

This file states it with `Φ = modulePullback` and `κ = modulePullbackCompIso` over the site
`s.site` of `s` (not over the site of `s.shrink`): `FG₁` is the first factor of `Ψ` in the target
square, with the functor of Stacks 03DX (2) over `s.site`, and the identity `F_c` is that of the
module attached to the Zariski reading of `(f ∘ x)^*𝒜_d`, spelled as the target of the
identification `ζ` of the slot `hsite` over `s.site`
(`…InvertibleTwistingRestriction.targetSquareSite_hsite`).  The statement is the type of the
instance of `Category.comp_id` (`type_of%`).

## Main results

* `…InvertibleTwistingRestriction.targetSquare_hΓ_site`: **the hypothesis `hΓ` of the target
  square at a scheme point `w` of `U(ψ)`, at `r = 𝟙`, over the site of `s`**.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

/-- **The hypothesis `hΓ` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`**, at `r = 𝟙`: the module `F_q = FG₁` attached to the canonical
identification `c_w^*q^*Z ≅ Z` on `W` (the first factor of `Ψ`, with the functor of
Stacks 03DX (2) over `s.site`), followed by `F_c = 𝟙` (the identity of the module attached to the
Zariski reading of `(f ∘ x)^*𝒜_d`, spelled as the target of `ζ` in the slot `hsite` over
`s.site`), is `FG₁`.  This is the hypothesis `hΓ` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over `s.site`. -/
theorem targetSquare_hΓ_site :
    type_of% (Category.comp_id
      (Y := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (zariskiReadingQcoh (B := s.site) (S := s.base) (hS := s.containsBase) W
          ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
            s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
            (locusPoint w ≫ f.hom) (d : ℤ)))).obj)
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.map
        (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
            (s.fibreToBase W (locusPoint w ≫ f.hom))
            (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
            (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
              (locusOpen_locusPoint w))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj ≫
          (Scheme.Modules.pullbackId _).hom.app
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
              (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) ⟶
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom) :=
  Category.comp_id _

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
