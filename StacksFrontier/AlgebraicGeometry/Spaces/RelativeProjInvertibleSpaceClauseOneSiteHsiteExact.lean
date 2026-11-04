module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSite

/-!
# The slot `hsite` of the target square of clause (1) of Stacks 0D2Z, spelled as the hypothesis

The target square of clause (1) of [Stacks, Tag 0D2Z] over the site of `s`
(`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`) takes as its
hypothesis `hsite` the naturality square of the identification `ρ_r` along `r = c ≫ q = 𝟙`.  The
slot is `…InvertibleTwistingRestriction.targetSquareSite_hsite`, the instance at the chart data of
`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom`, but that instance
spells the same objects differently from the hypothesis: the target of `ζ` is the module attached
to `zariskiReadingQcoh` rather than to `…RelativeProjSituation.pointPieceQcoh`, the identity `F_c`
is that of `Z` rather than of `(𝟭 _).obj Z`, `r` is the identity of `yonedaSpace W` rather than of
`⟨yoneda.obj W, _⟩`, and the étale point algebra is formed over `s.shrink.space` rather than
`s.space`.  Each is a definitional unfolding, but checking the whole equation across the two
spellings at once exhausts the heartbeat budget.

This file states the slot at variables in the spelling of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`: an arbitrary family `Φ` of inverse
images with comparisons `κ`, heterogeneously equal to `modulePullback` and
`modulePullbackCompIso`, and leaves `r`, `ρ_r`, `F_c` equal to `𝟙`, the unit law of Stacks 03LU
and `𝟙` (`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_of_heq`).  It is
proved by `subst` and the unit law at variables, so no factor is converted between two
spellings.  At the chart data the leaves are passed exactly as the target square passes them, so
the statement is the hypothesis `hsite` itself, and only the four leaf identities `Φ`, `κ`, `ρ_r`,
`F_c` (and `r = 𝟙`, `𝟭.obj Z = Z`) are checked, each on its own.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_of_heq`: the hypothesis
  `hsite` of the target square at `r = 𝟙`, for a family heterogeneously equal to
  `modulePullback`.
* `…InvertibleTwistingRestriction.targetSquareSite_hsite_exact`: **the hypothesis `hsite` of
  `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`, in its own
  spelling.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

section HsiteHEq

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Φ : ∀ {X Y : AlgebraicSpaces B S hS}, (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (κ : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z), Φ g ⋙ Φ f ≅ Φ (f ≫ g))

/-- **The hypothesis `hsite` of the target square at `r = 𝟙`, for a family heterogeneously
equal to `modulePullback`**: for `Φ = modulePullback` and `κ = modulePullbackCompIso` (as
heterogeneous equalities), `r = 𝟙`, `ρ_r` the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU and `F_c = 𝟙`,
the naturality square `(Φ r).map ζ ≫ ρ_r ≫ F_c = (κ r v ≫ τ_v) ≫ ζ` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` holds; it is
`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom`.  The binders are
those of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`, in its order, so that an
instance names its leaves as the target square does; `c`, `q` and `hcq : c ≫ q = r` fix `r` as
the target square does. -/
theorem modulePullback_map_comp_idIso_app_hom_comp_id_of_heq
    (hΦ : HEq (@Φ) (@modulePullback B S hS)) (hκ : HEq (@κ) (@modulePullbackCompIso B S hS))
    {R Fs Y : AlgebraicSpaces B S hS} {v : R ⟶ Y} {c : R ⟶ Fs} {q : Fs ⟶ R}
    {r : R ⟶ R} (hcq : c ≫ q = r) (hv : r ≫ v = v)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {Zr Zcq : Modules.{u, u} B S hS R.1 R.2}
    {ζ : (Φ v).obj M ≅ Zr} {ρr : (Φ r).obj Zr ≅ Zcq} {Fc : Zcq ⟶ Zr}
    {τv : (Φ (r ≫ v)).obj M ⟶ (Φ v).obj M} (hτv : τv = eqToHom (congrArg (fun k => (Φ k).obj M) hv))
    (hr : r = 𝟙 R) (hZcq : Zcq = Zr) (hρ : HEq ρr ((modulePullbackIdIso B S hS R).app Zr))
    (hFc : HEq Fc (𝟙 Zr)) :
    (Φ r).map ζ.hom ≫ ρr.hom ≫ Fc = ((κ r v).hom.app M ≫ τv) ≫ ζ.hom := by
  obtain rfl : @Φ = @modulePullback B S hS := eq_of_heq hΦ
  obtain rfl : @κ = @modulePullbackCompIso B S hS := eq_of_heq hκ
  subst hτv hr hZcq
  obtain rfl := eq_of_heq hρ
  obtain rfl := eq_of_heq hFc
  exact modulePullback_map_comp_idIso_app_hom_comp_id_eqToHom v M ζ

end HsiteHEq

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

/-- **The hypothesis `hsite` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`, in the spelling of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`**, at `r = c_w ≫ q = 𝟙`:
the inverse image along `𝟙` of the identification `ζ` of `(f ∘ x)^*𝒜_d` with the module attached
to `…RelativeProjSituation.pointPieceQcoh`, followed by the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU
and `F_c = 𝟙`, is the comparison `(𝟙)^*(f ∘ x)^* ≅ (𝟙 ≫ (f ∘ x))^*` at `𝒜_d`, the transport
along `𝟙 ≫ (f ∘ x) = f ∘ x` and `ζ`.  This is the slot
`…InvertibleTwistingRestriction.targetSquareSite_hsite` restated through
`AlgebraicGeometry.Space.modulePullback_map_comp_idIso_app_hom_comp_id_of_heq`, with the leaves
passed exactly as the target square passes them, so that its type is the hypothesis `hsite`. -/
theorem targetSquareSite_hsite_exact :
    type_of% (modulePullback_map_comp_idIso_app_hom_comp_id_of_heq
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase) HEq.rfl HEq.rfl
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (hv := Category.id_comp _)
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fc := 𝟙 _)
      (hτv := rfl)
      rfl rfl HEq.rfl HEq.rfl) :=
  modulePullback_map_comp_idIso_app_hom_comp_id_of_heq
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase) HEq.rfl HEq.rfl
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (hv := Category.id_comp _)
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ))
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fc := 𝟙 _)
      (hτv := rfl)
      rfl rfl HEq.rfl HEq.rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
