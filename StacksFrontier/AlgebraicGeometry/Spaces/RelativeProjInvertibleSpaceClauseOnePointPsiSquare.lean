module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneHone

/-!
# The square of `ψ` at the scheme point of `X` underlying a scheme point of `U(ψ)`

Let `w : W ⟶ U(ψ)` be a scheme point and let `x : W ⟶ X` be the scheme point underlying it. The
square of `ψ_d` at `x` says that the comparison `x^*(f^*𝒜_d) ≅ (x ≫ f)^*𝒜_d` of Stacks 03LU, the
transport along `x ≫ f = f ∘ x`, the identification `ζ` of `(f ∘ x)^*𝒜_d` with the module attached
to its Zariski reading and the module attached to the restriction `x^*ψ` of `ψ` in degree `d`
(`AlgebraicGeometry.Space.pointPsi`) compose to the inverse image along `x` of `ψ_d` followed by
the identification `x^*(ℒ^{⊗ d}) ≅ ((x^*ℒ)^{⊗ d})^a`.

## Main results

* `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app`: the square of
  `ψ_n` at a scheme point `x` of `X`, with the transport written as an `eqToHom`.
* `…InvertibleTwistingRestriction.compIso_hom_app_comp_map_pointPsi_app_locusPoint`: the square of
  `ψ_d` at the scheme point of `X` underlying a scheme point of `U(ψ)`.

## Implementation notes

The identification `ζ` is spelled as the fourth factor of the source identification
`…RelativeProjSituation.fibrePsiSourceIso`, as in
`…RelativeProjSituation.fibrePsiSourceIso_hom_eq`.

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

section PsiPoint

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

/-- `AlgebraicGeometry.Space.compIso_hom_app_comp_map_pointPsi_app` with the transport along
`x ≫ f = f ∘ x` written as an `eqToHom`. -/
theorem compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    (hN : ((etalePointAlgebra ((gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj A)
        T x).piece n).IsQuasicoherentOnSite) :
    (modulePullbackCompIso B S hS (pointHom x) f).hom.app (A.piece n) ≫
        eqToHom (congrArg (fun k => (modulePullback B S hS k).obj (A.piece n))
          (rfl : pointHom x ≫ f = pointHom (x ≫ f.hom))) ≫
        (zariskiReadingQuasicoherentIso T _
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.map
          (ObjectProperty.homMk ((pointPsi f A L ψ T x).app n) :
            zariskiReadingQcoh T _
              (isQuasicoherentOnSite_etalePointAlgebra_piece A hA (x ≫ f.hom) n)
              ⟶ pointLaurentPieceQcoh L T x n)).hom =
      (modulePullback B S hS (pointHom x)).map (ψ.app n) ≫ (pointTargetIso L T x n).hom :=
  compIso_hom_app_comp_map_pointPsi_app f A L ψ T x n hA hN

end PsiPoint

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

/-- The degree-`d` piece of the restriction of `f^*𝒜` to the scheme point of `X` underlying `w`
is quasi-coherent: it is isomorphic to the restriction of `𝒜_d` along `f ∘ x`. -/
theorem isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint :
    ((etalePointAlgebra ((gradedPull
      (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra) W (locusPoint w)).piece (d : ℤ)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@asIso _ _ _ _ ((pullbackEtalePointHom f s.shrink.algebra (Iso.refl _) W (locusPoint w)).app
      (d : ℤ))
      (isIso_pullbackEtalePointHom_app f s.shrink.algebra (Iso.refl _) W (locusPoint w)
        (d : ℤ))).symm
    (isQuasicoherentOnSite_etalePointAlgebra_piece s.shrink.algebra s.shrink.isQuasicoherent
      (locusPoint w ≫ f.hom) (d : ℤ))

/-- The square of `ψ_d` at the scheme point `x : W ⟶ X` underlying a scheme point `w` of `U(ψ)`:
the comparison `x^*(f^*𝒜_d) ≅ (x ≫ f)^*𝒜_d` of Stacks 03LU, the transport along `x ≫ f = f ∘ x`,
the identification of `(f ∘ x)^*𝒜_d` with the module attached to its Zariski reading (the fourth
factor of `…RelativeProjSituation.fibrePsiSourceIso`) and the module attached to `x^*ψ` in degree
`d` are the inverse image along `x` of `ψ_d` followed by `AlgebraicGeometry.Space.pointTargetIso`.
-/
theorem compIso_hom_app_comp_map_pointPsi_app_locusPoint :
    type_of% (compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app (hL := hL) f s.shrink.algebra L
      ψ W (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
      (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)) :=
  compIso_hom_app_comp_eqToHom_comp_map_pointPsi_app (hL := hL) f s.shrink.algebra L ψ W
    (locusPoint w) (d : ℤ) s.shrink.isQuasicoherent
    (isQuasicoherentOnSite_etalePointAlgebra_gradedPull_piece_locusPoint w d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
