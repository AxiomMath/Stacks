module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDegreeZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionAlgebra
public import StacksFrontier.RingTheory.Koszul.PowSheafAlgebra

/-!
# Inverse systems of algebras in degree zero

Let `C` be a category with the chaotic topology and `Λ` a commutative ring. An inverse system
`D : Cᵒᵖ ⥤ DifferentialGradedAlgebra Λ` of commutative algebras each concentrated in degree zero
gives, by `Stacks.ChaoticSite.systemAlgebra`, a sheaf of differential graded algebras over the
constant sheaf of rings, and also a presheaf of commutative rings `U ↦ D(U)`. This file records the
identification `SheafOfModules.DifferentialGradedModule.DegreeZero.Data` between the two, so that
the right differential graded modules over the system are the complexes of modules over the
presheaf of rings.

## Main definitions

* `Stacks.ChaoticSite.systemRing`: the presheaf of rings `U ↦ D(U)`.
* `Stacks.ChaoticSite.systemDegreeZeroData`: the identification, for a system of commutative
  algebras concentrated in degree zero.
* `Stacks.ChaoticSite.degreeZeroDiagram`: a presheaf of commutative rings, as a system of
  differential graded algebras over the lifted integers concentrated in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u u₁ v₁

namespace Stacks.ChaoticSite

variable {C : Type u₁} [Category.{v₁} C] {Λ : Type u} [CommRing Λ]

/-- The presheaf of rings `U ↦ D(U)` underlying an inverse system of differential graded
algebras. -/
def systemRing (D : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ) : Cᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (D.obj U).A
  map f := RingCat.ofHom (D.map f).toAlgebraHom.toRingHom
  map_id U := by
    ext x
    rw [D.map_id]
    rfl
  map_comp f g := by
    ext x
    rw [D.map_comp]
    rfl

/-- The restriction map of `systemRing D` along `f` is the underlying algebra map of `D.map f`. -/
@[simp]
theorem systemRing_map_apply (D : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : (D.obj U).A) : (systemRing D).map f x = (D.map f).toAlgebraHom x := rfl

/-- **An inverse system of commutative algebras concentrated in degree zero, as a sheaf of
differential graded algebras concentrated in degree zero**: the degree-zero sections of
`systemAlgebra D` over `U` are the elements of `D(U)`. -/
def systemDegreeZeroData (D : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ)
    (hzero : ∀ U, (D.obj U).grading 0 = ⊤)
    (hvan : ∀ U (n : ℤ), n ≠ 0 → (D.obj U).grading n = ⊥)
    (hcomm : ∀ U (x y : (D.obj U).A), x * y = y * x) :
    SheafOfModules.DifferentialGradedModule.DegreeZero.Data (systemAlgebra D) (systemRing D) where
  ψ U :=
    { toFun := fun x => (⟨x, (hzero U).symm ▸ Submodule.mem_top⟩ : (D.obj U).grading 0)
      invFun := fun x => Subtype.val (x : (D.obj U).grading 0)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  ψ_mul U x y := rfl
  ψ_one U := rfl
  ψ_map f x := rfl
  subsingleton n hn U := by
    change Subsingleton ((D.obj U).grading n)
    rw [hvan U n hn]
    infer_instance
  comm U x y := hcomm U x y

attribute [local instance] Stacks.uliftIntAlgebra

/-- A presheaf of commutative rings, as an inverse system of differential graded algebras over
the lifted integers, each concentrated in degree zero. -/
def degreeZeroDiagram (P : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} (ULift.{u, 0} ℤ) where
  obj U := DifferentialGradedAlgebra.degreeZero (ULift.{u, 0} ℤ) (P.obj U)
  map f := DifferentialGradedAlgebra.degreeZeroHom (Stacks.uliftIntAlgHom (P.map f).hom)
  map_id U := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq (by
    ext x
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (P.map_id U))
  map_comp f g := DifferentialGradedAlgebra.hom_eq_of_toAlgebraHom_eq (by
    ext x
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (P.map_comp f g))

/-- The identification of `systemAlgebra (degreeZeroDiagram P)` with `P` placed in degree zero. -/
def degreeZeroDiagramData (P : Cᵒᵖ ⥤ CommRingCat.{u}) :
    SheafOfModules.DifferentialGradedModule.DegreeZero.Data (systemAlgebra (degreeZeroDiagram P))
      (systemRing (degreeZeroDiagram P)) :=
  systemDegreeZeroData (degreeZeroDiagram P)
    (fun U => DifferentialGradedAlgebra.degreeZeroGrading_zero (ULift.{u, 0} ℤ) (P.obj U))
    (fun U _ hn => DifferentialGradedAlgebra.degreeZeroGrading_eq_bot (ULift.{u, 0} ℤ) (P.obj U) hn)
    (fun U x y => mul_comm (G := P.obj U) x y)

end Stacks.ChaoticSite

end
