module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationModuleColimitTheorem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LimitModulePullbackSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StageModuleFullness.HomRestriction

/-!
# The fullness clause for the pullback system of modules of a limit of algebraic spaces

Let `X = lim X_i` be the limit of a cofiltered system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms, indexed by a category small for the
site.  This file proves the fullness clause of the colimit assertion of Stacks 07V7 for the
pullback system `AlgebraicGeometry.Space.limitModulePullbackSystem`: a morphism between the
inverse images to `X` of two finitely presented modules on a stage is, through the comparison of
iterated inverse images, the inverse image of a morphism between their inverse images to a later
stage.  It is an input of the proof of Stacks 0GV2 and carries no `stacks` attribute: Stacks 07V7
is formalized elsewhere.

## Main results

* `AlgebraicGeometry.Space.limitModulePullbackSystem_fullness`: the fullness clause.

## Implementation notes

The proof is the fullness clause of the base's Stacks 07V7,
`AlgebraicGeometry.Space.finitePresentationModule_isColimit`
(`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FinitePresentationModuleColimitTheorem.lean`),
whose conclusion is phrased through the restriction
`AlgebraicGeometry.Space.moduleHomRestrict`; here it is read through the
comparisons `AlgebraicGeometry.Space.modulePullbackTriangle` of the pullback system.

## References

* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 0GV2](https://stacks.math.columbia.edu/tag/0GV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local irreducible] modulePullback modulePullbackTriangle

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
variable (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))

/-- **The fullness clause of the limit pullback system**, for quasi-compact and quasi-separated
stages: a morphism between the inverse images to the limit of two finitely presented modules on a
stage `k` is, through the comparison of iterated inverse images, the inverse image of a morphism
between their inverse images to a later stage `j`. -/
theorem limitModulePullbackSystem_fullness (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) :
    (limitModulePullbackSystem B S hS D hSize hHomSize hD hAffine).Fullness := by
  intro k M N hM hN φ
  obtain ⟨j, e, ψ, hψ⟩ := (finitePresentationModule_isColimit B S hS hZ D hSize hHomSize hD
    hAffine hqc hqs).2.1 k M N hM hN φ
  exact ⟨j, e, ψ, StageFullness.map_eq_of_moduleHomRestrict_eq _ _ _ _ _ _ hψ⟩

end AlgebraicGeometry.Space

end
