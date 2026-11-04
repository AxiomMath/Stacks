module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePointPsiSquare

/-!
# The slot `hTZ` of the target square of clause (1) of Stacks 0D2Z, in the syntax of the slot

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`, over the
site of `s` (`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`, the
instance of `AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at
`Φ = modulePullback s.site …` and `κ = modulePullbackCompIso s.site …`), takes as its hypothesis
`hTZ` the square of `ψ_d` at the scheme point `x : W ⟶ X` underlying `w`.

`…InvertibleTwistingRestriction.targetSquareSite_hTZ` states this square with the objects of
`AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app` (the transport ending
at `(x ≫ f)^*𝒜_d`, the source of `ζ` as the piece of the restricted algebra, the source of `ψ_d`
as the piece of `f^*𝒜`, the Zariski reading as `zariskiReadingQcoh`).  This file states it at the
objects of the slot: the transport along `x ≫ f = f ∘ x` ending at `(f ∘ x)^*𝒜_d`, `ζ` and `ψ_d`
at the types `(f ∘ x)^*𝒜_d ≅ Z` and `f^*𝒜_d ⟶ ℒ^{⊗ d}` of the slot, the Zariski reading as
`s.pointPieceQcoh`, and the point and its composite with `f` as elaborated in the chart data.

The bridge is `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app_of_eq`,
the same square at variables with every object and morphism of the slot a variable equal (or
heterogeneously equal) to the corresponding piece, closed by `subst`.  It is instantiated once at
the arguments of the slot, every equation `rfl`, and the statement is that instance's own type
(`type_of%`).

## Main results

* `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app_of_eq`: the square
  of `ψ_n` at a scheme point, at objects and morphisms equal to its pieces.
* `…InvertibleTwistingRestriction.targetSquareSite_hTZ_slot`: the hypothesis `hTZ` of the target
  square at a scheme point of `U(ψ)`, over the site of `s`, in the syntax of the slot.

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

namespace AlgebraicGeometry.Space

section PsiPointSlot

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y))
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f)).obj A)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L))
  (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) (n : ℤ)

set_option maxHeartbeats 0 in
-- Elaborating the module pullbacks in the statement and substituting along them exceeds the
-- default heartbeat bound.
/-- `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app` at objects and
morphisms equal to its pieces: for `v = (f ∘ x)` as a point, `M = 𝒜_n`, `L_x = ℒ^{⊗ n}`,
`ψ_d ≍ ψ_n`, `Z` the module attached to the Zariski reading of `(f ∘ x)^*𝒜_n`, `ζ` its
identification, `L_r` the module attached to the restriction of `ℒ^{⊗ n}`, `F ≍` the module
attached to `x^*ψ` in degree `n` and `θ ≍ pointTargetIso`, the comparison
`x^*(f^*M) ≅ (x ≫ f)^*M` of Stacks 03LU, the transport along `x ≫ f = v`, `ζ` and `F` are the
inverse image along `x` of `ψ_d` followed by `θ`: the shape of the hypothesis `hTZ` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback` and
`κ = modulePullbackCompIso`. -/
theorem compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app_of_eq
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite)
    {v : yonedaSpace B S hS T ⟶ Y} (hv : v = pointHom (x ≫ f.hom))
    (hxv : pointHom x ≫ f = v)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : M = A.piece n)
    {Lx : Modules.{u, u} B S hS X.1 X.2} {ψd : (modulePullback B S hS f).obj M ⟶ Lx}
    (hLx : Lx = SheafOfModules.GradedAlgebra.piece (R := structureRingSheaf B S hS X)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra (smallEtaleRingedTopos B S hS X).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L) n)
    (hψ : HEq ψd (ψ.app n))
    {Zr : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2}
    (hZr : Zr = ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
      (zariskiReadingQcoh T _
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n))).obj)
    {ζ : (modulePullback B S hS v).obj M ≅ Zr}
    (hζ : HEq ζ (zariskiReadingQuasicoherentIso T _
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)))
    {Lr : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2}
    (hLr : Lr = ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
      (pointLaurentPieceQcoh L T x n)).obj)
    {FG₂ : Zr ⟶ Lr}
    (hFG : HEq FG₂ ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (ObjectProperty.homMk ((pointPsi f A L ψ T x).app n) :
            zariskiReadingQcoh T _
                (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)
              ⟶ pointLaurentPieceQcoh L T x n)).hom)
    {θT : (modulePullback B S hS (pointHom x)).obj Lx ≅ Lr}
    (hθ : HEq θT (pointTargetIso L T x n)) :
    (modulePullbackCompIso B S hS (pointHom x) f).hom.app M ≫
        eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M) hxv) ≫ ζ.hom ≫ FG₂ =
      (modulePullback B S hS (pointHom x)).map ψd ≫ θT.hom := by
  subst hv hM hLx hZr hLr
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hζ
  obtain rfl := eq_of_heq hFG
  obtain rfl := eq_of_heq hθ
  exact compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app f A L ψ T x n hA hN

end PsiPointSlot

end AlgebraicGeometry.Space

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

set_option maxHeartbeats 0 in
-- Elaborating the `type_of%` statement, which spells every module pullback over the site of `s`
-- in full, exceeds the default heartbeat bound.
/-- **The hypothesis `hTZ` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`, in the syntax of the slot**: the comparison `x^*(f^*𝒜_d) ≅ (x ≫ f)^*𝒜_d` of
Stacks 03LU, the transport along `x ≫ f = f ∘ x`, the identification `ζ` of `(f ∘ x)^*𝒜_d` with
the module attached to its Zariski reading and the module attached to `x^*ψ` in degree `d` are the
inverse image along `x` of `ψ_d` followed by `AlgebraicGeometry.Space.pointTargetIso`, every object
and morphism spelled as in the arguments of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`. -/
theorem targetSquareSite_hTZ_slot :
    type_of% (compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app_of_eq
      (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (Y := s.space) (hL := hL)
      f s.shrink.algebra L ψ W (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
      (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom)) rfl rfl
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ)) rfl
      rfl (ψd := ψ.app (d : ℤ)) HEq.rfl
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj) rfl
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ))) HEq.rfl rfl
      (FG₂ := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk ((pointPsi (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := X) (Y := s.space) (hL := hL) f s.shrink.algebra L ψ W (locusPoint w)).app
              (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
              (hL := hL) L W (locusPoint w) (d : ℤ))).hom) HEq.rfl
      (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
        L W (locusPoint w) (d : ℤ)) HEq.rfl) :=
  compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app_of_eq
      (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (Y := s.space) (hL := hL)
      f s.shrink.algebra L ψ W (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
      (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)
      (v := pointHom (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
        (locusPoint w ≫ f.hom)) rfl rfl
      (M := SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.site s.base s.containsBase s.space) s.shrink.algebra (d : ℤ)) rfl
      rfl (ψd := ψ.app (d : ℤ)) HEq.rfl
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj) rfl
      (ζ := zariskiReadingQuasicoherentIso (B := s.site) (S := s.base) (hS := s.containsBase) W
        ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase) (X := s.space)
          s.shrink.algebra W (locusPoint w ≫ f.hom)).piece (d : ℤ))
        (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
          (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
          (locusPoint w ≫ f.hom) (d : ℤ))) HEq.rfl rfl
      (FG₂ := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk ((pointPsi (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := X) (Y := s.space) (hL := hL) f s.shrink.algebra L ψ W (locusPoint w)).app
              (d : ℤ)) :
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ) ⟶
            pointLaurentPieceQcoh (B := s.site) (S := s.base) (hS := s.containsBase) (X := X)
              (hL := hL) L W (locusPoint w) (d : ℤ))).hom) HEq.rfl
      (θT := pointTargetIso (B := s.site) (S := s.base) (hS := s.containsBase) (X := X) (hL := hL)
        L W (locusPoint w) (d : ℤ)) HEq.rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
