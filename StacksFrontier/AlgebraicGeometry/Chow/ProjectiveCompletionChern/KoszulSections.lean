module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartSection
public import StacksFrontier.AlgebraicGeometry.Modules.KoszulComplexExact
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Sections of the tautological kernel of the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])` with tautological surjection `u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)`, its
kernel `𝒦` and `φ : 𝒦 ⟶ 𝒪_E`. This file computes the values of `u` and of the projection
`π^*(𝒞 ⊕ 𝒪_X) ⟶ π^*𝒪_X = 𝒪_E` on pulled-back sections.

## Main results

* `Stacks.Chow.ProjectiveCompletion.taut_unitSection`: `u(π^*x) = ψ₁(x)`.
* `Stacks.Chow.ProjectiveCompletion.sndUnit_unitSection`: the projection sends `π^*x` to the
  pullback of the function `snd(x)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- The projection `π^*(𝒞 ⊕ 𝒪_X) ⟶ π^*𝒪_X = 𝒪_E`. -/
def sndUnit :
    (Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞) ⟶
      (show (space 𝒞).Modules from SheafOfModules.unit (space 𝒞).ringCatSheaf) :=
  (Scheme.Modules.pullback (proj 𝒞)).map (snd 𝒞) ≫ (Scheme.Modules.pullbackUnitIso (proj 𝒞)).hom

/-- The map `φ : 𝒦 ⟶ 𝒪_E` is the inclusion of the kernel of `u` followed by `sndUnit`. -/
theorem koszulMap_eq : koszulMap 𝒞 = kernel.ι (taut 𝒞) ≫ sndUnit 𝒞 := rfl

/-- **The pullback of the structure sheaf, read on sections**: the isomorphism
`π^*𝒪_X ≅ 𝒪_E` sends the pullback of a function to its pullback as a function. -/
theorem pullbackUnitIso_unitSection {Y Z : Scheme.{u}} (f : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    (Scheme.Modules.pullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U))
        (unitSection f (SheafOfModules.unit Z.ringCatSheaf) U a) =
      f.app U a := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit
    (f := (Scheme.Modules.pullbackUnitIso f).hom)
  rw [Scheme.Modules.pullbackUnitIso_homEquiv] at h
  exact (congrArg (fun t => t.val.app (op U) a) h).symm

/-- **The projection `π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E` on a pulled-back section** is the pullback of the
function given by its second component. -/
theorem sndUnit_unitSection (U : X.Opens) (x : Γ(module 𝒞, U)) :
    (sndUnit 𝒞).val.app (op (proj 𝒞 ⁻¹ᵁ U)) (unitSection (proj 𝒞) (module 𝒞) U x) =
      (proj 𝒞).app U (Scheme.Modules.Hom.app (snd 𝒞) U x) := by
  change (Scheme.Modules.pullbackUnitIso (proj 𝒞)).hom.val.app (op (proj 𝒞 ⁻¹ᵁ U))
    (((Scheme.Modules.pullback (proj 𝒞)).map (snd 𝒞)).val.app (op (proj 𝒞 ⁻¹ᵁ U))
      (unitSection (proj 𝒞) (module 𝒞) U x)) = _
  rw [GenuineChern.unitSection_pullback_map]
  exact pullbackUnitIso_unitSection (proj 𝒞) U _

/-- **The tautological surjection on a pulled-back section** is the degree-one homogeneous
section map. -/
theorem taut_unitSection (U : X.Opens) (x : Γ(module 𝒞, U)) :
    (taut 𝒞).val.app (op (proj 𝒞 ⁻¹ᵁ U)) (unitSection (proj 𝒞) (module 𝒞) U x) =
      ((twistData 𝒞).ψ 1).val.app (op U)
        ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op U) x) :=
  GenuineChern.tautologicalMap_unitSection (module 𝒞) (bundlePieces (module 𝒞)) U x

end Stacks.Chow.ProjectiveCompletion

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **Lifting a germ killed by `u` to the kernel.** A germ at `ξ` of a section of
`π^*(𝒞 ⊕ 𝒪_X)` which `u` sends to zero is the image of a germ of `𝒦`. -/
theorem exists_kernel_germ (ξ : space 𝒞) (W : (space 𝒞).Opens) (hξ : ξ ∈ W)
    (v : ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).val.obj (op W))
    (hv : (taut 𝒞).val.app (op W) v = 0) :
    ∃ k : ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ),
      PresheafOfModules.stalkMapL ξ (kernel.ι (taut 𝒞)).val k =
        TopCat.Presheaf.germ ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).val.presheaf
          W ξ hξ v := by
  have hS := (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).1
    (shortExact_taut 𝒞) ξ
  refine (ShortComplex.moduleCat_exact_iff _).1 hS.exact _ ?_
  change PresheafOfModules.stalkMapL ξ (taut 𝒞).val _ = 0
  exact (PresheafOfModules.stalkMapL_germ ξ (taut 𝒞).val W hξ v).trans
    ((congrArg _ hv).trans (map_zero _))

/-- The stalk map of a composite of morphisms of sheaves of modules. -/
theorem stalkMapL_comp {Y : Scheme.{u}} {A B D : SheafOfModules.{u} Y.ringCatSheaf} (f : A ⟶ B)
    (g : B ⟶ D) (y : Y) (k : ↑(TopCat.Presheaf.stalk A.val.presheaf y)) :
    PresheafOfModules.stalkMapL y (f ≫ g).val k =
      PresheafOfModules.stalkMapL y g.val (PresheafOfModules.stalkMapL y f.val k) := by
  change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf _).map (f.val ≫ g.val))) k = _
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- **The functional `φ_ξ` is the projection to `𝒪_E` read on the image in
`π^*(𝒞 ⊕ 𝒪_X)`.** -/
theorem stalkDual_koszulMap (ξ : space 𝒞)
    (k : ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ)) :
    Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
        (koszulMap 𝒞) ξ k =
      Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ
        (PresheafOfModules.stalkMapL ξ (kernel.ι (taut 𝒞)).val k) :=
  congrArg (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv
    (space 𝒞).sheaf ξ) (stalkMapL_comp (kernel.ι (taut 𝒞)) (sndUnit 𝒞) ξ k)

end Stacks.Chow.ProjectiveCompletion
