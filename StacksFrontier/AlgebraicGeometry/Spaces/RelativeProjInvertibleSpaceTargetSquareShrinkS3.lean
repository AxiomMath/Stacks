module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneInstanceB

/-!
# The composition law `hcomp` of the target square of clause (1) of Stacks 0D2Z

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) needs the composition law of the
identifications `g^*(M^a) ≅ (g^*M)^a` of the inverse image of an attached module
(`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`) along the section
`c_w : W ⟶ W ×_Y P` and the structure morphism `q : W ×_Y P ⟶ W`, as its hypothesis `hcomp`.
This file states that law in the spelling of `hcomp` (the comparison of Stacks 03LU as
`(modulePullbackCompIso _ _).hom.app`, the transport as an `eqToHom`) at variables, read off
`AlgebraicGeometry.Space.compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom`, and its
instance at `c_w` and `q` over the site of `s.shrink`.

## Main results

* `Space.compIso_hom_app_comp_eqToHom_comp_modulePullbackRepresentedQuasicoherentIso_hom`:
  the composition law of the identifications `g^*(M^a) ≅ (g^*M)^a`, in the spelling of `hcomp`.
* `…InvertibleTwistingRestriction.targetSquare_hcomp`: its instance at `c_w` and `q`, the
  hypothesis `hcomp` of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at
  `Φ = modulePullback`, `κ = modulePullbackCompIso` over the site of `s.shrink`, with
  `r = c_w ≫ q` and `ρ_r` the identification along `c_w ≫ q`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` composes**, with the comparison of Stacks 03LU
written `(modulePullbackCompIso _ _).hom.app` and the transport to the represented composite an
`eqToHom` (the spelling of the hypothesis `hcomp` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`): the comparison
`h^*g^*(M^a) ≅ (h ≫ g)^*(M^a)` followed by the identification along `h ≫ g` is the inverse image
along `h` of the identification along `g`, the identification along `h`, and the module attached
to the comparison `h^*g^*M ≅ (h ≫ g)^*M` of pullbacks. -/
theorem compIso_hom_app_comp_eqToHom_comp_modulePullbackRepresentedQuasicoherentIso_hom
    {W V U : BigFppfOver B S hS} (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g)).hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≫
      eqToHom (congrArg (fun k : representedAlgebraicSpace B S hS W ⟶
          representedAlgebraicSpace B S hS U => (modulePullback B S hS k).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
        (algebraicSpacesComp_representedSpaceMap B S hS h g)) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M).hom =
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS h
        (quasicoherentPullbackObj B S hS g M)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
          (quasicoherentPullbackCompIso B S hS h g M).hom).hom :=
  compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS h g M

end Represented

end AlgebraicGeometry.Space

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

/-- **The composition law `hcomp` of the target square of clause (1) at a scheme point `w` of
`U(ψ)`**: the identifications `g^*(M^a) ≅ (g^*M)^a` along the section
`c_w : W ⟶ W ×_Y P` and the structure morphism `q : W ×_Y P ⟶ W`, at the restriction
`((f ∘ x)^*𝒜)_d` of `𝒜_d` to the scheme point of `Y` under `w`, compose to the identification
along `c_w ≫ q`.  This is the hypothesis `hcomp` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso` over the site of `s.shrink`, with `r = c_w ≫ q`. -/
theorem targetSquare_hcomp :
    type_of% (compIso_hom_app_comp_eqToHom_comp_modulePullbackRepresentedQuasicoherentIso_hom
      s.shrink.site s.shrink.base s.shrink.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
      (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) :=
  compIso_hom_app_comp_eqToHom_comp_modulePullbackRepresentedQuasicoherentIso_hom
    s.shrink.site s.shrink.base s.shrink.containsBase
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
    (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
    (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
