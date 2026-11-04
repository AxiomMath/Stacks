module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetSiteSlot

/-!
# The slot `hcomp` of the target square of clause (1) of Stacks 0D2Z over `s.site`

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`), instantiated with every inverse
image and comparison over the site `s.site` of the situation (`Φ = modulePullback s.site …`,
`κ = modulePullbackCompIso s.site …`), takes at `r = 𝟙` the hypothesis `hcomp`.  It is recorded
here as the instance at `B := s.site` of its statement at variables (`type_of%`), so that no factor
is compared across the two spellings `s.site` and `s.shrink.site` of the site.

## Main results

* `…InvertibleTwistingRestriction.targetSquare_hcomp_site`: the hypothesis `hcomp`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

/-- **The hypothesis `hcomp` of the target square at a scheme point `w` of `U(ψ)`, at `r = 𝟙`, over
`s.site`**:
`AlgebraicGeometry.Space.compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom` at
the section `c_w`, the structure morphism `W ×_Y P ⟶ W` and the piece of the point algebra, with
every functor and identification over the site of the situation. -/
theorem targetSquare_hcomp_site :
    type_of% (compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom (B := s.site)
      (S := s.base) (hS := s.containsBase)
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
      ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))
      (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w) (locusOpen_locusPoint w))
      (ObjectProperty.hom_ext _
          ((yoneda.map_comp
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))).symm.trans
        ((congrArg yoneda.map
              ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w)
                (locusOpen_locusPoint w))).trans
            (yoneda.map_id W))))
      (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) :=
  (compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom (B := s.site) (S := s.base)
      (hS := s.containsBase)
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
      ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))
      (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w) (locusOpen_locusPoint w))
      (ObjectProperty.hom_ext _
          ((yoneda.map_comp
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))).symm.trans
        ((congrArg yoneda.map
              ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w)
                (locusOpen_locusPoint w))).trans
            (yoneda.map_id W))))
      (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)) :)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
