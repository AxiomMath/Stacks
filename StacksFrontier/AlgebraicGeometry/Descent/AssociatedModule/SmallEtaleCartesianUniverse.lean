module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian

/-!
# A quasi-coherent module on the small étale site is cartesian, at every section universe

Let `S` be a scheme contained in a big étale site `B`.
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite` proves
the forward implication of Descent, Proposition 03DX (2) at `τ = étale` for sheaves of modules on
the small étale site of `S` whose sections lie in the universe `u` of the schemes: for a
quasi-coherent `𝒢` and a morphism `T ⟶ T'` of objects with affine underlying schemes, the
base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.

The same implication holds for sheaves of modules whose sections lie in any universe containing
`u`, in particular in `u + 1`, where the higher direct images of the algebraic stacks of
Stacks 0765 live.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite_univ`:
  **a quasi-coherent sheaf of modules on the small étale site of a scheme, with sections in any
  universe containing that of the schemes, is cartesian between affine objects.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent sheaf of modules on the small étale site of a scheme is cartesian between
affine objects, with its sections in any universe containing that of the schemes.**  For a
morphism `f : T ⟶ T'` of objects of `S_étale` whose underlying schemes are affine, the
base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.

This is `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`
with the sections of `𝒢` in `Type (max m u)` rather than `Type u`. -/
theorem bijective_restrictionBaseChange_of_isQuasicoherentOnSite_univ
    (G : SheafOfModules.{max m u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T'))
    (f : T ⟶ T') :
    Function.Bijective
      (restrictionBaseChange (R := commStructurePresheaf B S hS) G.val f.op) := by
  have hds : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have hcc : (SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  have hover : ∀ X : SmallAffineEtale B S hS,
      (Over.post (X := X) (SmallAffineEtale.inclusion B S hS)).IsContinuous
        ((SmallAffineEtale.topology B S hS).over X)
        ((topology B S hS).over ((SmallAffineEtale.inclusion B S hS).obj X)) :=
    fun X => by
      have _ := Stacks.Sites.overPost_isDenseSubsite
        (J := SmallAffineEtale.topology B S hS) (K := topology B S hS)
        (SmallAffineEtale.inclusion B S hS) X
      infer_instance
  have h₁ := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (structureSheaf B S hS) G hG
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation h₁
  -- Stacks 0H04 for the chart rings
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, m}
    B S hS _ _ h₂
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) f)
  have h₄ := bijective_restrictionBaseChange_of_uliftForPresentation.{u + 1, u, u, m, u + 1}
    (affineChartRings B S hS) _ _ _ h₃
  have h₅ := bijective_restrictionBaseChange_of_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (commStructurePresheaf B S hS) _ G _ h₄
  rwa [(SmallAffineEtale.inclusion B S hS).map_preimage] at h₅

end AlgebraicGeometry.SmallEtale

end
