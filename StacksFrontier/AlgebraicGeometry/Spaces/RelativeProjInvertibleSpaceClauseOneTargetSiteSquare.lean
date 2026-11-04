module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneInstanceB
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetSiteBridge

/-!
# The target square of clause (1) of Stacks 0D2Z, read over the site of `s`

Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` follows from its target square
`K ≫ Ψ ≫ T = w^*b` (`…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'`), stated with
every inverse image, comparison of Stacks 03LU and attached-module functor over the site
`s.shrink.site`.  The generic target square
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) is naturally instantiated over
`s.site`.  The two sites are equal by definition (`…RelativeProjSituation.shrink_site`), but a
comparison of the two readings of the whole square is expensive; this file carries the square
across with heterogeneously equal leaves, compared one at a time.

## Main results

* `…InvertibleTwistingRestriction.htgt_of_site_square`: the target square over `s.shrink.site`
  from the target square over `s.site`.
* `…InvertibleTwistingRestriction.clauseOnePoint_of_siteSquare`: **clause (1) at a scheme point,
  from the target square over `s.site`.**

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

section Generic

/-- **The morphism of represented algebraic spaces, read over a second spelling of the site**:
`yoneda.map g` as a morphism of algebraic spaces over `B₁` and over `B₂ = B₁` are heterogeneously
equal for heterogeneously equal `g`. -/
theorem representedSpaceMap_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {T₁ T₁' : BigFppfOver B₁ S₁ hS₁} {g₁ : T₁' ⟶ T₁}
    {T₂ T₂' : BigFppfOver B₂ S₂ hS₂} {g₂ : T₂' ⟶ T₂}
    (hT : HEq T₁ T₂) (hT' : HEq T₁' T₂') (hg : HEq g₁ g₂) :
    HEq (representedSpaceMap B₁ S₁ hS₁ g₁) (representedSpaceMap B₂ S₂ hS₂ g₂) := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hT' hg
  rfl

/-- **The identification `g^*(M^a) ≅ (g^*M)^a`, read over a second spelling of the site**: its
underlying morphisms over `B₁` and over `B₂ = B₁` are heterogeneously equal for heterogeneously
equal leaves. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_heq_of_site {B₁ B₂ : BigFppfSite.{u}}
    (hB : B₁ = B₂) {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁}
    {hS₂ : B₂.Contains S₂} {T₁ T₁' : BigFppfOver B₁ S₁ hS₁} {τ₁ : T₁' ⟶ T₁}
    {M₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₁ S₁ hS₁).obj T₁).ringCatSheaf).FullSubcategory}
    {T₂ T₂' : BigFppfOver B₂ S₂ hS₂} {τ₂ : T₂' ⟶ T₂}
    {M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B₂ S₂ hS₂).obj T₂).ringCatSheaf).FullSubcategory}
    (hT : HEq T₁ T₂) (hT' : HEq T₁' T₂') (hτ : HEq τ₁ τ₂) (hM : HEq M₁ M₂) :
    HEq (modulePullbackRepresentedQuasicoherentIso B₁ S₁ hS₁ τ₁ M₁).hom
      (modulePullbackRepresentedQuasicoherentIso B₂ S₂ hS₂ τ₂ M₂).hom := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hT hT' hτ hM
  rfl

end Generic

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

/-- **A leaf of the target square over the two spellings of the site**: the transport along
`π_{U(ψ)} = r ≫ π`, over `s.site` and over `s.shrink.site` (equal by `shrink_site`), are
heterogeneously equal. -/
theorem siteSquare_heq_e :
    HEq
      (eqToHom (congrArg (fun k => (modulePullback s.site s.base
        s.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
          (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm))
      (eqToHom (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base
        s.shrink.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
          (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm)) :=
  eqToHom_heq_of_site s.shrink_site.symm s.shrink_base.symm _ _ HEq.rfl HEq.rfl HEq.rfl

/-- **A leaf of the target square over the two spellings of the site**: the inverse comparison
`(r ≫ π)^*𝒜_d ≅ r^*π^*𝒜_d` of Stacks 03LU, over `s.site` and over `s.shrink.site` (equal by
`shrink_site`), are heterogeneously equal. -/
theorem siteSquare_heq_i :
    HEq
      (((modulePullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv)
      (((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) :=
  modulePullbackCompIso_inv_app_heq_of_site s.shrink_site.symm s.shrink_base.symm HEq.rfl HEq.rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **A leaf of the target square over the two spellings of the site**: the comparison
`w^*r^* ≅ c_w^*φ^*` of the two factorisations of `w ≫ r`, over `s.site` and over `s.shrink.site`
(equal by `shrink_site`), are heterogeneously equal. -/
theorem siteSquare_heq_τ :
    HEq
      ((modulePullbackCompTransportIso (B := s.site) (S := s.base)
        (hS := s.containsBase) (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
        (pointHom_comp_invertibleSpaceMorphism w) (s.psiSourceQcoh (d : ℤ)).obj).hom)
      ((modulePullbackCompTransportIso (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
        (pointHom_comp_invertibleSpaceMorphism w) (s.psiSourceQcoh (d : ℤ)).obj).hom) :=
  modulePullbackCompTransportIso_hom_heq_of_site s.shrink_site.symm s.shrink_base.symm HEq.rfl
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **A leaf of the target square over the two spellings of the site**: the section
`c_w : W ⟶ W ×_Y P` as a morphism of represented algebraic spaces, over `s.site` and over
`s.shrink.site` (equal by `shrink_site`), are heterogeneously equal. -/
theorem siteSquare_heq_c :
    HEq
      (representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))) :=
  representedSpaceMap_heq_of_site s.shrink_site.symm s.shrink_base.symm HEq.rfl HEq.rfl HEq.rfl

/-- **A leaf of the target square over the two spellings of the site**: the identification
`c_w^*(M^a) ≅ (c_w^*M)^a` of the inverse image of an attached module, over `s.site` and over
`s.shrink.site` (equal by `shrink_site`), are heterogeneously equal. -/
theorem siteSquare_heq_ρ :
    HEq
      ((modulePullbackRepresentedQuasicoherentIso s.site s.base
        s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom)
      ((modulePullbackRepresentedQuasicoherentIso s.shrink.site s.shrink.base
        s.shrink.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom) :=
  modulePullbackRepresentedQuasicoherentIso_hom_heq_of_site s.shrink_site.symm s.shrink_base.symm
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl

set_option maxHeartbeats 0 in
-- Carrying the whole square at the chart data from `s.site` to `s.shrink.site` exceeds the
-- default heartbeat budget.
/-- **The target square of clause (1) at a scheme point `w` of `U(ψ)`, from its reading over
`s.site`**: the square `K ≫ Ψ ≫ T = w^*b` (the hypothesis `htgt` of
`…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'`, every functor and comparison
over `s.shrink.site`) follows from the same square with every inverse image, comparison of
Stacks 03LU and attached-module functor over `s.site` — the conclusion of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback s.site`,
`κ = modulePullbackCompIso s.site` at the chart data.  The two sites are equal by definition
(`…RelativeProjSituation.shrink_site`); the square is carried across by
`…InvertibleTwistingRestriction.targetSquare_of_site_heq`, its leaves compared one
by one. -/
theorem htgt_of_site_square
    (hsq :
      ((modulePullback s.site s.base s.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
          (eqToHom (congrArg (fun k => (modulePullback s.site s.base
            s.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
              (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm) ≫
            ((modulePullbackCompIso s.site s.base s.containsBase
              ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
              s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) ≫
        (modulePullbackCompTransportIso (B := s.site) (S := s.base)
          (hS := s.containsBase) (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
          ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
          (representedSpaceMap s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
          (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
          (pointHom_comp_invertibleSpaceMorphism w) (s.psiSourceQcoh (d : ℤ)).obj).hom ≫
        (modulePullback s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).map
          (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom ≫
        (modulePullbackRepresentedQuasicoherentIso s.site s.base
          s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom) ≫
      (((representedQuasicoherentSchemeEquivalence s.site s.base
          s.containsBase W).functor.map
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
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.site s.base
          s.containsBase W).functor.map
        (ObjectProperty.homMk ((pointPsi f s.shrink.algebra L ψ W (locusPoint w)).app (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh L W (locusPoint w) (d : ℤ))).hom) ≫
      (chartTargetIso w (d : ℤ)).hom =
        (modulePullback s.site s.base s.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
      ((modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
          (eqToHom (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base
            s.shrink.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
              (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm) ≫
            ((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
              ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
              s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) ≫
        (modulePullbackCompTransportIso (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
          ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
          (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
          (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
          (pointHom_comp_invertibleSpaceMorphism w) (s.psiSourceQcoh (d : ℤ)).obj).hom ≫
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
          (representedSpaceMap s.shrink.site s.shrink.base s.shrink.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).map
          (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom ≫
        (modulePullbackRepresentedQuasicoherentIso s.shrink.site s.shrink.base
          s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom) ≫
      (((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
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
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
          s.shrink.containsBase W).functor.map
        (ObjectProperty.homMk ((pointPsi f s.shrink.algebra L ψ W (locusPoint w)).app (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh L W (locusPoint w) (d : ℤ))).hom) ≫
      (chartTargetIso w (d : ℤ)).hom =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d) :=
  targetSquare_of_site_heq s.shrink_site.symm s.shrink_base.symm hsq HEq.rfl HEq.rfl HEq.rfl
    HEq.rfl (siteSquare_heq_c w)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (siteSquare_heq_e d) (siteSquare_heq_i d) (siteSquare_heq_τ w d) HEq.rfl
    (siteSquare_heq_ρ w d) HEq.rfl HEq.rfl HEq.rfl HEq.rfl

/-- **Clause (1) of Stacks 0D2Z at a scheme point `w : W ⟶ U(ψ)`, from the target square over
`s.site`**: `…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'` with its hypothesis
`htgt` supplied by `…InvertibleTwistingRestriction.htgt_of_site_square`. -/
theorem clauseOnePoint_of_siteSquare
    (hsq :
      ((modulePullback s.site s.base s.containsBase
          (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
          (eqToHom (congrArg (fun k => (modulePullback s.site s.base
            s.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
              (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm) ≫
            ((modulePullbackCompIso s.site s.base s.containsBase
              ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
              s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) ≫
        (modulePullbackCompTransportIso (B := s.site) (S := s.base)
          (hS := s.containsBase) (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
          ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
          (representedSpaceMap s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
          (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
          (pointHom_comp_invertibleSpaceMorphism w) (s.psiSourceQcoh (d : ℤ)).obj).hom ≫
        (modulePullback s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).map
          (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom ≫
        (modulePullbackRepresentedQuasicoherentIso s.site s.base
          s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom) ≫
      (((representedQuasicoherentSchemeEquivalence s.site s.base
          s.containsBase W).functor.map
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
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.site s.base
          s.containsBase W).functor.map
        (ObjectProperty.homMk ((pointPsi f s.shrink.algebra L ψ W (locusPoint w)).app (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh L W (locusPoint w) (d : ℤ))).hom) ≫
      (chartTargetIso w (d : ℤ)).hom =
        (modulePullback s.site s.base s.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOnePsiLeg s f L ψ d) :=
  clauseOnePoint_of_targetSquare' Px w d (htgt_of_site_square w d hsq)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
