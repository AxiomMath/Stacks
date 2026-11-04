module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.FibreSurjectivity

/-!
# Global functions on the fibre are the base change of global functions

Let `g : Y ⟶ Spec R` be separated, `p` a prime of `R` and `Y_p` the base change of `Y` to
`κ(p)`. Let `D` be the Čech model of `𝒪_Y` for a finite affine open cover with affine finite
intersections. If every degree-zero cocycle of `D ⊗_R κ(p)` comes from a cocycle of `D`, and the
base change `Z⁰(D) ⊗_R κ(p) → D⁰ ⊗_R κ(p)` of the inclusion of cocycles is injective, then the
canonical map of `κ(p)`-algebras `κ(p) ⊗_R Γ(Y, 𝒪_Y) → Γ(Y_p, 𝒪_{Y_p})` is bijective.

This is the identification `H⁰(E) ⊗ κ(s) = H⁰(X_s, 𝒪_{X_s})` of the proof of [Stacks, Tag 0G7Y],
read on the Čech model, and it transports étaleness of the fibre to `κ(p) ⊗_R Γ(Y, 𝒪_Y)`.

## Main results

* `StacksDraft.Perfect.GeomReducedFibre.etale_fiber_globalSections`: if `Γ(Y_p, 𝒪_{Y_p})` is
  étale over `κ(p)`, then so is `κ(p) ⊗_R Γ(Y, 𝒪_Y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
  {Y Yp : Scheme.{u}} {g : Y ⟶ Spec (.of R)} [IsSeparated g]
  {fp : Yp ⟶ Spec (.of p.ResidueField)} {gp : Yp ⟶ Y}
  (hsq : IsPullback gp fp g (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))))
  {I : Type u} [Finite I] (U : I → Y.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

omit [IsSeparated g] in
include hsq in
/-- The pullback of the image of `r ∈ R` is the image of `r` in `κ(p)`. -/
theorem appTop_globalRingHom_apply (r : R) :
    gp.appTop ((Stacks.Cech.globalRingHom g).hom r) =
      (Stacks.Cech.globalRingHom fp).hom (algebraMap R p.ResidueField r) := by
  have h := congrArg (fun φ => φ.hom r)
    (Stacks.Cech.baseRingHom_comp_app (algebraMap R p.ResidueField) g fp gp hsq ⊤)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rwa [← baseRingHom_top_apply, ← baseRingHom_top_apply]

omit [IsSeparated g] [Finite I] in
/-- The Čech model of a global function is a degree-zero cocycle. -/
theorem d_sectionsToModel (a : Γ(Y, ⊤)) :
    (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).d 0 1
      (letI := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤;
        sectionsToModel g U hU (Scheme.unitModule Y) a) = 0 :=
  let := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤
  (range_sectionsToModel g U hU (Scheme.unitModule Y)).le (LinearMap.mem_range_self _ _)

/-- The degree-zero cocycle of the Čech model of a global function. -/
def globalSectionsToCycles (a : Γ(Y, ⊤)) :
    (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).cycles 0 :=
  (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).cyclesMk
    (letI := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤;
      sectionsToModel g U hU (Scheme.unitModule Y) a) 1 (by simp) (d_sectionsToModel U hU a)

omit [IsSeparated g] [Finite I] in
/-- The cocycle `globalSectionsToCycles U hU a` includes into the degree-zero cochains as the
Čech model of `a`. -/
theorem iCycles_globalSectionsToCycles (a : Γ(Y, ⊤)) :
    (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0
        (globalSectionsToCycles U hU a) =
      (letI := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤;
        sectionsToModel g U hU (Scheme.unitModule Y) a) :=
  HomologicalComplex.i_cyclesMk (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)) _ _ _ _

omit [IsSeparated g] [Finite I] in
/-- Every degree-zero cocycle of the Čech model comes from a unique global function. -/
theorem globalSectionsToCycles_bijective :
    Function.Bijective (globalSectionsToCycles (g := g) U hU) := by
  let := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤
  have hiinj : Function.Injective
      ((baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ⟨fun a b h => sectionsToModel_injective g U hU (Scheme.unitModule Y) ?_, fun z => ?_⟩
  · have := congrArg ((baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0) h
    rwa [iCycles_globalSectionsToCycles, iCycles_globalSectionsToCycles] at this
  · obtain ⟨a, ha⟩ : (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0 z ∈
        LinearMap.range (sectionsToModel g U hU (Scheme.unitModule Y)) := by
      refine (range_sectionsToModel g U hU (Scheme.unitModule Y)).ge ?_
      rw [LinearMap.mem_ker]
      have := congrArg (fun m => m z)
        ((baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles_d 0 1)
      simp only [ModuleCat.comp_apply] at this
      exact this.trans (by simp)
    exact ⟨a, hiinj ((iCycles_globalSectionsToCycles U hU a).trans ha)⟩

omit [IsSeparated g] in
/-- **Global functions are the degree-zero cocycles of the Čech model**, as an `R`-linear
equivalence, `R` acting on `Γ(Y, 𝒪_Y)` through `g`. -/
def globalSectionsCyclesEquiv :
    letI := (Stacks.Cech.globalRingHom g).hom.toAlgebra
    Γ(Y, ⊤) ≃ₗ[R] (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).cycles 0 :=
  letI : Algebra R Γ(Y, ⊤) := (Stacks.Cech.globalRingHom g).hom.toAlgebra
  letI := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤
  have hiinj : Function.Injective
      ((baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  LinearEquiv.ofBijective
    { toFun := globalSectionsToCycles U hU
      map_add' := fun a b => hiinj (by
        rw [map_add, iCycles_globalSectionsToCycles, iCycles_globalSectionsToCycles,
          iCycles_globalSectionsToCycles]
        exact map_add (sectionsToModel g U hU (Scheme.unitModule Y)) a b)
      map_smul' := fun r a => hiinj (by
        rw [map_smul, iCycles_globalSectionsToCycles, iCycles_globalSectionsToCycles,
          RingHom.id_apply]
        have : ((r • a : Γ(Y, ⊤)) : Γ(Scheme.unitModule Y, ⊤)) =
            r • (show Γ(Scheme.unitModule Y, ⊤) from a) := by
          change (Stacks.Cech.globalRingHom g).hom r * a =
            (Stacks.Cech.baseRingHom g ⊤).hom r • (show Γ(Scheme.unitModule Y, ⊤) from a)
          rw [baseRingHom_top_apply]
          rfl
        rw [this]
        exact map_smul (sectionsToModel g U hU (Scheme.unitModule Y)) r _) }
    (globalSectionsToCycles_bijective U hU)

omit [IsSeparated g] [Finite I] in
/-- The cocycle `globalSectionsCyclesEquiv U hU a` includes into the degree-zero cochains as the
Čech model of `a`. -/
theorem iCycles_globalSectionsCyclesEquiv (a : Γ(Y, ⊤)) :
    (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0
        (globalSectionsCyclesEquiv U hU a) =
      (letI := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤;
        sectionsToModel g U hU (Scheme.unitModule Y) a) :=
  iCycles_globalSectionsToCycles U hU a

include hsq hUaff in
/-- If every degree-zero cocycle of `D ⊗_R κ(p)` comes from a cocycle of the Čech model `D`, and
`Z⁰(D) ⊗_R κ(p) → D⁰ ⊗_R κ(p)` is injective, then `κ(p) ⊗_R Γ(Y, 𝒪_Y)` is étale over `κ(p)`
whenever `Γ(Y_p, 𝒪_{Y_p})` is. -/
theorem etale_fiber_globalSections
    (hS : DegreeZeroCyclesSurjective (algebraMap R p.ResidueField)
      (baseAlternatingCechComplex g U hU (Scheme.unitModule Y)))
    (hinj : Function.Injective ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap R p.ResidueField)).map
        ((baseAlternatingCechComplex g U hU (Scheme.unitModule Y)).iCycles 0))) :
    letI := (Stacks.Cech.globalRingHom g).hom.toAlgebra
    letI := (Stacks.Cech.globalRingHom fp).hom.toAlgebra
    Algebra.Etale p.ResidueField Γ(Yp, ⊤) → Algebra.Etale p.ResidueField (p.Fiber Γ(Y, ⊤)) := by
  let : Algebra R Γ(Y, ⊤) := (Stacks.Cech.globalRingHom g).hom.toAlgebra
  let : Algebra p.ResidueField Γ(Yp, ⊤) := (Stacks.Cech.globalRingHom fp).hom.toAlgebra
  intro hét
  let : Algebra R Γ(Yp, ⊤) :=
    ((Stacks.Cech.globalRingHom fp).hom.comp (algebraMap R p.ResidueField)).toAlgebra
  have : IsScalarTower R p.ResidueField Γ(Yp, ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := Stacks.Cech.sectionsModule g (Scheme.unitModule Y) ⊤
  let φ := algebraMap R p.ResidueField
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let D := baseAlternatingCechComplex g U hU (Scheme.unitModule Y)
  let j := sectionsToModel g U hU (Scheme.unitModule Y)
  let gpR : Γ(Y, ⊤) →ₐ[R] Γ(Yp, ⊤) :=
    { toRingHom := (gp.appTop.hom : Γ(Y, ⊤) →+* Γ(Yp, ⊤))
      commutes' := fun r => appTop_globalRingHom_apply p hsq r }
  let θ : p.Fiber Γ(Y, ⊤) →ₐ[p.ResidueField] Γ(Yp, ⊤) :=
    Algebra.TensorProduct.lift (Algebra.ofId p.ResidueField _) gpR fun _ _ => Commute.all _ _
  let L := globalSectionsCyclesEquiv (g := g) U hU
  let e₁ : p.ResidueField ≃ₗ[R] (ModuleCat.restrictScalars φ).obj (ModuleCat.of _ p.ResidueField) :=
    { toFun := fun c => c
      invFun := fun c => c
      map_add' := fun _ _ => rfl
      map_smul' := fun r c => Algebra.smul_def r c
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := TensorProduct.congr e₁ L
  let Ψ : p.Fiber Γ(Y, ⊤) →+ (extendScalarsCx φ D).X 0 :=
    (F.map (D.iCycles 0)).hom.toAddMonoidHom.comp G.toAddMonoidHom
  have hΨinj : Function.Injective Ψ := hinj.comp G.injective
  have hΨ : ∀ (c : p.ResidueField) (a : Γ(Y, ⊤)), Ψ (c ⊗ₜ a) = c ⊗ₜ[R, φ] j a := by
    intro c a
    show F.map (D.iCycles 0) (c ⊗ₜ[R, φ] L a) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact congrArg _ (iCycles_globalSectionsCyclesEquiv U hU a)
  have hkey : ∀ t, fibreCochain φ hsq U hU hUaff (θ t) = Ψ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, fibreCochain_zero, map_zero]
    | tmul c a =>
      rw [Algebra.TensorProduct.lift_tmul, hΨ]
      show fibreCochain φ hsq U hU hUaff (c • gp.appTop a) = _
      rw [fibreCochain_smul, fibreCochain_appTop]
      refine (ModuleCat.ExtendScalars.smul_tmul φ c 1 _).trans ?_
      rw [mul_one]
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, fibreCochain_add, h₁, h₂, map_add]
  have hθ : Function.Bijective θ := by
    refine ⟨fun t₁ t₂ h => hΨinj ?_, fun w => ?_⟩
    · rw [← hkey, ← hkey, h]
    · obtain ⟨y, hy⟩ := hS _ (d_fibreCochain φ hsq U hU hUaff w)
      obtain ⟨t, rfl⟩ := G.surjective y
      refine ⟨t, fibreCochain_injective φ hsq U hU hUaff ?_⟩
      rwa [hkey]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective θ hθ).symm

end StacksDraft.Perfect.GeomReducedFibre

end
