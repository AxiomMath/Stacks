module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneChart

/-! # probe -/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open AlgebraicGeometry

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤) (d : ℕ)

/-- The section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of a scheme point `w` of `U(ψ)`, read on schemes,
followed by the structure morphism `W ×_Y Proj_Y(𝒜) ⟶ W`, is the identity. -/
theorem toScheme_map_chartSection_comp_fibreToBase :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        ((ofUnitalHom s f L ψ).chartSection x hx) ≫ s.fibreToBase W (x ≫ f.hom) = 𝟙 _ :=
  ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map
        ((ofUnitalHom s f L ψ).chartSection_fibreHom x hx)).trans
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map_id W))

/-- **Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`, on the scheme `W`.**  For
a morphism `c : W ⟶ W ×_Y Proj_Y(𝒜)` of schemes which is a section of the structure morphism and
lies over `r_w` (the section `c_w` of `…InvertibleTwistingRestriction.chartSection`, read on
schemes, is such a `c`, by `…toScheme_map_chartSection_comp_fibreToBase` and
`…toScheme_map_chartSection_toRelativeProj`), the inverse image along `c` of `ψ` of Tag 01NR in
adjoint form (`…RelativeProjSituation.psiChartSchemeHomOfAdjoint`, written out as
`AlgebraicGeometry.Space.pullbackAdjointPsi`), followed by the contraction
`c^*((W ×_Y P ⟶ P)^*𝒪(d)) ≅ r_w^*𝒪(d)` and `θ_w` of Tag 01O9
(`…InvertibleTwistingRestriction.chartTheta`, written out as `…GradedPowerMap.thetaOnSection`) —
that is, the underlying morphism of `…InvertibleTwistingRestriction.chartSchemeTheta` — is the
contraction `c^*(π_W^*((f ∘ w)^*𝒜)_d) ≅ ((f ∘ w)^*𝒜)_d` followed by the adjoint transpose of the
restriction `w^*ψ`.

This is `…GradedPowerMap.pullbackAdjointPsi_comp_thetaOnSection` — clause (1) of Tag 01O9 in
morphism form — transported along `c` by
`…pullback_map_pullbackAdjointPsi_comp_canHom_comp`. -/
theorem pullback_map_pullbackAdjointPsi_comp_chartTheta
    (c : (BigFppfOver.toScheme s.site s.base s.containsBase).obj W ⟶
      (BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.relativeProjPoints.fibre W (x ≫ f.hom)))
    (hcr : c ≫ s.toRelativeProj W (x ≫ f.hom) =
      (ofUnitalHom s f L ψ).chartLift x hx ≫
        (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).globalMorphism
          (relativeProj (s.relativeProjPoints.algebra W (x ≫ f.hom))))
    (hcb : c ≫ s.fibreToBase W (x ≫ f.hom) =
      𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)) :
    (Scheme.Modules.pullback c).map
        (AlgebraicGeometry.Space.pullbackAdjointPsi
          (s.relativeProjPoints.algebra W (x ≫ f.hom)) (s.toRelativeProj W (x ≫ f.hom))
          (s.fibreToBase W (x ≫ f.hom)) (s.fibreToBase_eq W (x ≫ f.hom)) d) ≫
        Stacks.AlgebraicGeometry.ModuleLimits.canHom c (s.toRelativeProj W (x ≫ f.hom))
          ((ofUnitalHom s f L ψ).chartLift x hx ≫
            (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra W (x ≫ f.hom)))) hcr
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra W (x ≫ f.hom))).algebra.piece
            (d : ℤ)) ≫
        (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).thetaOnSection
          ((ofUnitalHom s f L ψ).chartLift x hx)
          ((ofUnitalHom s f L ψ).chartLift_ι x hx) (d : ℤ) =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom c (s.fibreToBase W (x ≫ f.hom))
          (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)) hcb
          ((s.relativeProjPoints.algebra W (x ≫ f.hom)).piece (d : ℤ)) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))).homEquiv _ _).symm
          ((toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).ψ d) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
          ((ofUnitalHom s f L ψ).line W x) d).hom :=
  pullback_map_pullbackAdjointPsi_comp_canHom_comp
    (s.relativeProjPoints.algebra W (x ≫ f.hom)) (s.toRelativeProj W (x ≫ f.hom))
    (s.fibreToBase W (x ≫ f.hom)) (s.fibreToBase_eq W (x ≫ f.hom)) c
    ((ofUnitalHom s f L ψ).chartLift x hx ≫
      (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra W (x ≫ f.hom)))) hcr
    (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W)) hcb
    (GradedPowerMap.eq_comp_globalMorphism_comp_toBase
      (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x))
      ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx)) d _ _
    (GradedPowerMap.pullbackAdjointPsi_comp_thetaOnSection
      (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x))
      ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx) d
      (GradedPowerMap.eq_comp_globalMorphism_comp_toBase
        (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x))
        ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx)))

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
