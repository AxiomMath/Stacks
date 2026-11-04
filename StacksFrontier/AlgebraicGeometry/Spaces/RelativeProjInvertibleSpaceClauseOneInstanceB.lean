module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneProjLegFactors
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePaste

/-!
# Clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`, from its target square

Clause (1) of [Stacks, Tag 0D2Z] on `U(ψ)` is descended from the identity
`w^*(ψ_P leg) ≫ χ_w = w^*(ψ leg)` at the scheme points `w : W ⟶ U(ψ)` (the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`), where
`χ_w = (chartTargetIso w) ∘ θ_w^a ∘ (chartSourceIso w)` is the chart map.  This file instantiates
the paste of the three squares of that identity
(`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares`) at the chart maps, stage
by stage, over the site of `s.shrink` throughout:

* the source square at the chart maps
  (`…InvertibleTwistingRestriction.clauseOneSource_square_chartMap`), the instance of
  `…InvertibleTwistingRestriction.clauseOneSourceShaped_square` at the source identification
  `…chartSourceIso` and the three factors of the `ψ_P` leg;
* the middle square at the chart maps
  (`…InvertibleTwistingRestriction.clauseOneMiddle_square_chartMap`), clause (1) of Stacks 01O9 on
  `W` on the attached modules, its right-hand side split into its two factors;
* the point identity (`…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'`), with the
  target square as its only hypothesis.

## Main results

* `…InvertibleTwistingRestriction.clauseOnePoint_of_targetSquare'`: **the point identity of
  clause (1) at `w`, granted the target square.**

## Implementation notes

The leaves of the source square are spelled through `(ofUnitalHom s f L ψ).locusSpace X.property`
and `⟨yoneda.obj W, _⟩`, those of the legs and the chart map through `locusSpaceOfUnitalHom` and
`yonedaSpace`; the two are compared only at the leaves.  The leading factor `w^*(pre₁ ≫ pre₂)` of
the source identification holds an `eqToHom`, and is compared factor by factor
(`…InvertibleTwistingRestriction.comp_heq_of_site`): comparing it whole exhausts the budget.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

section Generic

/-- **The inverse comparison of Stacks 03LU, read over a second spelling of the site**: the
underlying morphisms of `(a ≫ b)^*M ≅ a^*b^*M` over `B₁` and over `B₂ = B₁` are heterogeneously
equal for heterogeneously equal leaves. -/
theorem modulePullbackCompIso_inv_app_heq_of_site {B₁ B₂ : BigFppfSite.{u}} (hB : B₁ = B₂)
    {S₁ S₂ : Scheme.{u}} (hSS : S₁ = S₂) {hS₁ : B₁.Contains S₁} {hS₂ : B₂.Contains S₂}
    {X₁ Y₁ Z₁ : AlgebraicSpaces B₁ S₁ hS₁} {a₁ : X₁ ⟶ Y₁} {b₁ : Y₁ ⟶ Z₁}
    {M₁ : Modules.{u, u} B₁ S₁ hS₁ Z₁.1 Z₁.2}
    {X₂ Y₂ Z₂ : AlgebraicSpaces B₂ S₂ hS₂} {a₂ : X₂ ⟶ Y₂} {b₂ : Y₂ ⟶ Z₂}
    {M₂ : Modules.{u, u} B₂ S₂ hS₂ Z₂.1 Z₂.2}
    (hX : HEq X₁ X₂) (hY : HEq Y₁ Y₂) (hZ : HEq Z₁ Z₂) (ha : HEq a₁ a₂) (hb : HEq b₁ b₂)
    (hM : HEq M₁ M₂) :
    HEq ((modulePullbackCompIso B₁ S₁ hS₁ a₁ b₁).app M₁).inv
      ((modulePullbackCompIso B₂ S₂ hS₂ a₂ b₂).app M₂).inv := by
  subst hB hSS
  obtain rfl : hS₁ = hS₂ := rfl
  subst hX hY hZ
  subst ha hb hM
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

/-- **The source square of clause (1) at a scheme point `w` of `U(ψ)`, at the chart maps**:
`…InvertibleTwistingRestriction.clauseOneSource_square_of_chartSourceIso` with the leading factors
`pre₁`, `pre₂` the transport along `r ≫ π = π_{U(ψ)}` and the comparison of Stacks 03LU, both over
the site of `s.shrink`, and the source identification `K` the composite of its four factors: the
hypothesis `hsrc` of `…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares`. -/
theorem clauseOneSource_square_chartMap :
    type_of% (clauseOneSource_square_of_chartSourceIso Px w d
      (pre₁ := eqToHom (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base
        s.shrink.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
          (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm))
      (pre₂ := ((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) _ rfl
      (A' := pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
      (hab' := pointHom_comp_invertibleSpaceMorphism w) _ rfl HEq.rfl HEq.rfl rfl rfl rfl rfl) :=
  clauseOneSource_square_of_chartSourceIso Px w d
      (pre₁ := eqToHom (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base
        s.shrink.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
          (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm))
      (pre₂ := ((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) _ rfl
      (A' := pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
      (hab' := pointHom_comp_invertibleSpaceMorphism w) _ rfl HEq.rfl HEq.rfl rfl rfl rfl rfl

/-- **The middle square of clause (1) at a scheme point `w` of `U(ψ)`, at the chart maps**: on
the attached modules over the site of `s.shrink`, the inverse image along `c_w` of `ψ` of
Tag 01NR followed by `θ_w` is the canonical identification followed by `w^*ψ` in degree `d`
(`quasicoherentPullbackMap_fibrePsiQcohHom_comp_chartSchemeTheta_eq_pointPsi`), the right-hand
side as the composite of its two factors: the hypothesis `hsch` of
`…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares`. -/
theorem clauseOneMiddle_square_chartMap :
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base s.shrink.containsBase
        W).functor.map (quasicoherentPullbackMap s.shrink.site s.shrink.base s.shrink.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.fibrePsiQcohHom W (locusPoint w ≫ f.hom) d))).hom ≫
      ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase W).functor.map
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (d : ℤ))).hom =
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base s.shrink.containsBase
        W).functor.map
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
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base s.shrink.containsBase
        W).functor.map
      (ObjectProperty.homMk ((pointPsi f s.shrink.algebra L ψ W (locusPoint w)).app (d : ℤ)) :
        s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
          pointLaurentPieceQcoh L W (locusPoint w) (d : ℤ))).hom :=
  (functor_map_hom_comp_map_hom
    (representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base s.shrink.containsBase
      W).functor
    (quasicoherentPullbackMap_fibrePsiQcohHom_comp_chartSchemeTheta_eq_pointPsi s f L ψ
      (locusPoint w) (locusOpen_locusPoint w) d)).trans
    (functor_map_hom_comp_map_hom
      (representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base s.shrink.containsBase
        W).functor rfl).symm

set_option maxHeartbeats 800000 in
-- The `HEq.rfl` leaves of the paste are checked by unfolding the large module composites.
/-- **Clause (1) of Stacks 0D2Z at a scheme point `w : W ⟶ U(ψ)`, granted the target square**: the
inverse image along `w` of the `ψ_P` leg followed by the chart map `χ_w` is the inverse image of
the `ψ` leg (the hypothesis `hone` of
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points` at `Px`, `d`, `W`, `w`),
as soon as the source identification of the square, followed by the two factors of the right-hand
side of the middle square and by `chartTargetIso w`, is the inverse image of the `ψ` leg.  The
instance of `…InvertibleTwistingRestriction.modulePullback_map_comp_eq_of_squares` at
`…clauseOneSource_square_chartMap`, `…clauseOneProjLeg_eq_comp_comp` and
`…clauseOneMiddle_square_chartMap`. -/
theorem clauseOnePoint_of_targetSquare'
    (htgt :
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
          (clauseOnePsiLeg s f L ψ d)) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (clauseOnePsiLeg s f L ψ d) :=
  modulePullback_map_comp_eq_of_squares (B₁ := s.shrink.site) (B₂ := s.shrink.site) rfl
    (S₁ := s.shrink.base) (S₂ := s.shrink.base) rfl (hS₁ := s.shrink.containsBase)
    (hS₂ := s.shrink.containsBase)
    (Y₁ := (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.shrink.site s.shrink.base
      s.shrink.containsBase W⟩ : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase))
    (clauseOneSource_square_chartMap Px w d : _)
    (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w) (clauseOneProjLeg s f L ψ Px d)
    (clauseOneProjLeg_eq_comp_comp Px d : _)
    (clauseOnePsiLeg s f L ψ d) (chartMap Px w (d : ℤ))
    (J₂ := (chartSourceIso Px w (locusOpen_locusPoint w) (d : ℤ)).hom)
    (Θ₂ := ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase W).functor.map
      (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (d : ℤ))).hom)
    (T₂ := (chartTargetIso w (d : ℤ)).hom) (rfl : _)
    (clauseOneMiddle_square_chartMap w d : _) (htgt : _)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (modulePullbackCompIso_inv_app_heq_of_site s.shrink_site s.shrink_base
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
    (modulePullback_map_heq_of_site s.shrink_site s.shrink_base
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
    HEq.rfl
    (comp_comp_comp_heq_of_site rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (modulePullback_map_heq_of_site rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        (comp_heq_of_site rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl))
      (modulePullbackCompTransportIso_hom_heq_of_site rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
        HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      (modulePullback_map_heq_of_site rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl)
      HEq.rfl)
    HEq.rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
