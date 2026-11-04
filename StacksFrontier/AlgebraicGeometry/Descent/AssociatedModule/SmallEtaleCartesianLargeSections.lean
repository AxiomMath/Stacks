module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian

/-!
# A quasi-coherent module on the small étale site is cartesian, at a large module universe

`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite` proves
that a quasi-coherent sheaf of modules on the small étale site of a scheme `S` is cartesian between
affine objects: for a morphism `T ⟶ T'` of affine objects of `S_ét` the base-change comparison
`Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective. It is stated for module sections in the universe `u`
of the schemes.

The argument does not need that: its only universe-sensitive input,
`AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite`
(Stacks 0H04 on the small affine étale site), already holds at every module universe
`max m (u + 1)`. This file states the cartesian property for module sections at
`max (u + 1) m`, the universe at which the quasi-coherent modules of the stacks chapters live
(a direct image of modules on an algebraic stack has its sections in `Type (u + 1)`).

## Main results

* `bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse`
  (namespace `AlgebraicGeometry.SmallEtale`):
  **a quasi-coherent sheaf of modules on the small étale site of a scheme, with sections in
  `Type (max (u + 1) m)`, is cartesian between affine objects.**

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent sheaf of modules on the small étale site of a scheme is cartesian between
affine objects, at the module universe `max (u + 1) m`.** For a morphism `f : T ⟶ T'` of objects
of `S_ét` whose underlying schemes are affine, the base-change comparison
`Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.

The proof is the one of
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`: restrict
to the affine subsite, raise the universe of the sections, apply Stacks 0H04 for the chart rings,
and descend bijectivity through the two steps. -/
theorem bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse
    (G : SheafOfModules.{max (u + 1) m} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T'))
    (f : T ⟶ T') :
    Function.Bijective
      (restrictionBaseChange.{u + 1, u, u, max (u + 1) m} (R := commStructurePresheaf B S hS)
        G.val f.op) := by
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
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, max (u + 1) m}
    B S hS _ _ h₂
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) f)
  have h₄ :=
    bijective_restrictionBaseChange_of_uliftForPresentation.{u + 1, u, u, max (u + 1) m, u + 1}
    (affineChartRings B S hS) _ _ _ h₃
  have h₅ := bijective_restrictionBaseChange_of_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (commStructurePresheaf B S hS) _ G _ h₄
  rwa [(SmallAffineEtale.inclusion B S hS).map_preimage] at h₅

end AlgebraicGeometry.SmallEtale

end
