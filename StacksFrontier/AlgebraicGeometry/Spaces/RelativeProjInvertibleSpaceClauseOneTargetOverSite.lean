module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHT
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHTZ
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHsite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceSiteSlotsC2
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetUnitSlots
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedKernelIdealSquareMapAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantPullback

/-!
# The target square of clause (1) of Stacks 0D2Z at a scheme point, over the site of `s`

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` is the
instance of the target square at variables
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) at the chart data.  This file
proves that instance with every inverse image, comparison of Stacks 03LU and identification of
Stacks 03DX (2) taken over the site of `s` (not of `s.shrink`): `Φ = modulePullback s.site …`,
`κ = modulePullbackCompIso s.site …`, at `r = c_w ≫ q = 𝟙`.

## Main results

* `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`: the target square
  of clause (1) at a scheme point `w` of `U(ψ)`, over the site of `s`, from its slots.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
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

/-- **The section `c_w` of the fibre `q : W ×_Y P ⟶ W`, on represented algebraic spaces over the
site of `s`**: `c_w ≫ q = 𝟙`. -/
theorem representedSpaceMap_chartSection_comp_fibreHom_overSite :
    CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (representedSpaceMap s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))) =
      𝟙 (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) :=
  (algebraicSpacesComp_representedSpaceMap s.site s.base s.containsBase _ _).trans
    ((congrArg (representedSpaceMap s.site s.base s.containsBase)
      ((ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w)
        (locusOpen_locusPoint w))).trans (representedSpaceMap_id s.site s.base s.containsBase W))

set_option maxHeartbeats 0 in
-- elaborating the `type_of%` statement, a large application with many named arguments
/-- **The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`,
over the site of `s`, from its slots**:
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback s.site …` and
`κ = modulePullbackCompIso s.site …`, at the chart data (`r = c_w ≫ q = 𝟙`, `F_c = 𝟙`, `F_Γ` the
canonical identification of the middle square), with the source identification, the middle
factors, `chartTargetIso` and the `ψ` leg in place, the remaining hypotheses (`hcomp`,
`hsite`, `hTZ`, `hτ₁`, `hχ`, `hT`, `hb`) left open. -/
theorem clauseOneTarget_square_overSite_of_slots :
    type_of% (comp_comp_eq_map_of_target_squares
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase)
      (fun a b c M => modulePullbackCompIso_assoc_app s.site s.base s.containsBase a b c M)
      (fun a b c M => modulePullbackCompIso_assoc_inv_app s.site s.base s.containsBase a b c M)
      (fun a b c M =>
        modulePullbackCompIso_map_inv_comp_hom_app s.site s.base s.containsBase a b c M)
      (fun a b c M =>
        modulePullbackCompIso_inv_comp_map_hom_app s.site s.base s.containsBase a b c M)
      (p := pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := locusSpaceOfUnitalHom s f L ψ) w)
      (a := (ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
      (π := s.relativeProjSpaceHom)
      (ι := locusInclusionOfUnitalHom s f L ψ) (f := f)
      (hk := (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm)
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (φ := s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
      (hab := pointHom_comp_invertibleSpaceMorphism w)
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom))
      (hφ := s.fibreToSpaceHom_comp_relativeProjSpaceHom W (locusPoint w ≫ f.hom))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (hv := Category.id_comp _)
      (x := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
        (locusPoint w))
      (hx := pointHom_locusPoint w) (hxv := rfl)
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (ψd := ψ.app (d : ℤ))
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρq := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρc := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fq := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
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
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom)
      (Fc := 𝟙 _)
      (FG₂ := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk ((pointPsi (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := X) (Y := s.space) (hL := hL) f s.shrink.algebra L ψ W (locusPoint w)).app
              (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
              (hL := hL) L W
              (locusPoint w) (d : ℤ))).hom)
      (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
        L W (locusPoint w) (d : ℤ))
      (hτZ := rfl) (hτv := rfl) (hτx := rfl) (hΓ := Category.comp_id _)
      (τ₁ := (modulePullbackCompTransportIso (B := s.site) (S := s.base) (hS := s.containsBase)
        (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := locusSpaceOfUnitalHom s f L ψ) w)
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
        (pointHom_comp_invertibleSpaceMorphism w)
        ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
          (SheafOfModules.GradedAlgebra.piece
            (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra
            (d : ℤ)))).hom)
      (χ := (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom)
      (T := (chartTargetIso w (d : ℤ)).hom) (b := clauseOnePsiLeg s f L ψ d)
      (hK := rfl) (hκ₁ := rfl) (hΨ := rfl)) :=
  comp_comp_eq_map_of_target_squares
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase)
      (fun a b c M => modulePullbackCompIso_assoc_app s.site s.base s.containsBase a b c M)
      (fun a b c M => modulePullbackCompIso_assoc_inv_app s.site s.base s.containsBase a b c M)
      (fun a b c M =>
        modulePullbackCompIso_map_inv_comp_hom_app s.site s.base s.containsBase a b c M)
      (fun a b c M =>
        modulePullbackCompIso_inv_comp_map_hom_app s.site s.base s.containsBase a b c M)
      (p := pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := locusSpaceOfUnitalHom s f L ψ) w)
      (a := (ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
      (π := s.relativeProjSpaceHom)
      (ι := locusInclusionOfUnitalHom s f L ψ) (f := f)
      (hk := (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm)
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (φ := s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
      (hab := pointHom_comp_invertibleSpaceMorphism w)
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom))
      (hφ := s.fibreToSpaceHom_comp_relativeProjSpaceHom W (locusPoint w ≫ f.hom))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (hv := Category.id_comp _)
      (x := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
        (locusPoint w))
      (hx := pointHom_locusPoint w) (hxv := rfl)
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (ψd := ψ.app (d : ℤ))
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρq := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρc := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fq := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
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
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom)
      (Fc := 𝟙 _)
      (FG₂ := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk ((pointPsi (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := X) (Y := s.space) (hL := hL) f s.shrink.algebra L ψ W (locusPoint w)).app
              (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
              (hL := hL) L W
              (locusPoint w) (d : ℤ))).hom)
      (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
        L W (locusPoint w) (d : ℤ))
      (hτZ := rfl) (hτv := rfl) (hτx := rfl) (hΓ := Category.comp_id _)
      (τ₁ := (modulePullbackCompTransportIso (B := s.site) (S := s.base) (hS := s.containsBase)
        (pointHom (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := locusSpaceOfUnitalHom s f L ψ) w)
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
        (pointHom_comp_invertibleSpaceMorphism w)
        ((modulePullback s.site s.base s.containsBase s.relativeProjSpaceHom).obj
          (SheafOfModules.GradedAlgebra.piece
            (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra
            (d : ℤ)))).hom)
      (χ := (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom)
      (T := (chartTargetIso w (d : ℤ)).hom) (b := clauseOnePsiLeg s f L ψ d)
      (hK := rfl) (hκ₁ := rfl) (hΨ := rfl)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
