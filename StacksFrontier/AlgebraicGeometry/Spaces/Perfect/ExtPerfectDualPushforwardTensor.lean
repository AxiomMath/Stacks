module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTower
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages

/-!
# The dual of `Rf_* RSheafHom(E, 𝒢^•)` in the spelling of the base change of Stacks 0A1K

For a perfect object `E`, the object `K = Rf_* RSheafHom(E, 𝒢^•)` of Stacks 0DKK and 08JN
(`AlgebraicGeometry.Space.extPerfectDirectImageObj`) is `Rf_*(E^∨ ⊗^L 𝒢^•)` (Stacks 08JJ), with
`Rf_*` the derived direct image of the morphism of small étale ringed topoi
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePushforward`), in which the base change of
Stacks 0A1K is stated. This file records that identification, and the corresponding one of the
duals `K^∨`.

## Main definitions

* `AlgebraicGeometry.Space.dualPushforwardTensorIsoExtPerfectDirectImageObj`:
  `Rf_*(E^∨ ⊗^L 𝒢^•) ≅ Rf_* RSheafHom(E, 𝒢^•)` for a perfect `E`.
* `AlgebraicGeometry.Space.extPerfectDualObjIsoDualPushforwardTensor`: the dual isomorphism
  `(Rf_* RSheafHom(E, 𝒢^•))^∨ ≅ (Rf_*(E^∨ ⊗^L 𝒢^•))^∨`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*(E^∨ ⊗^L 𝒢^•) ≅ Rf_* RSheafHom(E, 𝒢^•)` for a perfect `E`**, the first `Rf_*` being the
derived direct image of the morphism of small étale ringed topoi. -/
def dualPushforwardTensorIsoExtPerfectDirectImageObj (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj
          (DerivedCategory.Q.obj G)) ≅
      extPerfectDirectImageObj B S hS f E G :=
  (smallEtaleDerivedModulePushforwardIso B S hS f).app _ ≪≫
    (derivedSheafHomPushforwardIsoTensorDual B S hS f E hE (DerivedCategory.Q.obj G)).symm

/-- **`(Rf_* RSheafHom(E, 𝒢^•))^∨ ≅ (Rf_*(E^∨ ⊗^L 𝒢^•))^∨` for a perfect `E`**: the dual of
`AlgebraicGeometry.Space.dualPushforwardTensorIsoExtPerfectDirectImageObj`. -/
def extPerfectDualObjIsoDualPushforwardTensor (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    extPerfectDualObj B S hS f E G ≅
      smallEtaleDerivedDual B S hS Y ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj
          (DerivedCategory.Q.obj G))) :=
  ((smallEtaleDerivedSheafHom B S hS Y).mapIso
    (dualPushforwardTensorIsoExtPerfectDirectImageObj B S hS f E hE G).op).app _

end AlgebraicGeometry.Space

end
