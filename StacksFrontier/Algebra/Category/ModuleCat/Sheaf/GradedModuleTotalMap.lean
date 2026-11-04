module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule

/-!
# A homomorphism of graded modules on its homogeneous sections

Let `A` be a commutative sheaf of `ℤ`-graded algebras over a sheaf of rings on a site and let
`f : M ⟶ N` be a homomorphism of right graded `A`-modules. Over each object `U` of the site the
homogeneous sections of `M` assemble into a module `Stacks.GradedModule.Total` over the ring
`Stacks.GradedAlgebra.Total` of homogeneous sections of `A`, and `f` assembles degreewise into a
linear map between them.

This file builds that linear map, computes the homogeneous components of a section of the total
module, and shows that the linear map is injective as soon as `f` is injective on the sections
of every homogeneous piece.

## Main definitions

* `SheafOfModules.GradedModule.totalFun` — the degree-`n` component of a section of the total
  module.
* `SheafOfModules.GradedModule.totalAddHom` and
  `SheafOfModules.GradedModule.totalLinearMap` — the degreewise assembly of `f`, as an additive
  map and as a linear map over the ring of homogeneous sections of `A`.

## Main results

* `SheafOfModules.GradedModule.totalFun_totalAddHom` — the assembled map acts componentwise.
* `SheafOfModules.GradedModule.injective_totalAddHom` — degreewise injectivity suffices.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A : GradedAlgebra.{w, w} R}

/-- **The degree-`n` component of a section of the total module.** The total module is a direct
sum, so a section of it has a homogeneous component in every degree, almost all zero. -/
abbrev totalFun (M : GradedModule.{w, w, w} A) (U : Cᵒᵖ)
    (t : M.toPresheafGradedModule.Total U) (n : ℤ) : (M.piece n).val.obj U :=
  (show DirectSum ℤ fun k => ((M.piece k).val.obj U : Type w) from t) n

section Component

variable {M : GradedModule.{w, w, w} A} {U : Cᵒᵖ}

/-- Every homogeneous component of the zero section of the total module is zero. -/
@[simp]
theorem totalFun_zero (n : ℤ) : totalFun M U 0 n = 0 := rfl

/-- The degree-`n` component of a sum of sections is the sum of their degree-`n` components. -/
@[simp]
theorem totalFun_add (t t' : M.toPresheafGradedModule.Total U) (n : ℤ) :
    totalFun M U (t + t') n = totalFun M U t n + totalFun M U t' n := by
  show (show DirectSum ℤ fun k => ((M.piece k).val.obj U : Type w) from t + t') n = _
  exact DFinsupp.add_apply _ _ n

/-- The degree-`n` component of the inclusion of a degree-`n` section `x` is `x`. -/
@[simp]
theorem totalFun_incl (n : ℤ) (x : (M.piece n).val.obj U) :
    totalFun M U (M.toPresheafGradedModule.incl n x) n = x := by
  show (DirectSum.of (fun k => ((M.piece k).val.obj U : Type w)) n x) n = x
  exact DirectSum.of_eq_same (β := fun k => ((M.piece k).val.obj U : Type w)) n x

/-- For `k ≠ n`, the degree-`n` component of the inclusion of a degree-`k` section is zero. -/
theorem totalFun_incl_of_ne {k n : ℤ} (h : k ≠ n) (x : (M.piece k).val.obj U) :
    totalFun M U (M.toPresheafGradedModule.incl k x) n = 0 := by
  classical
  show (DirectSum.of (fun j => ((M.piece j).val.obj U : Type w)) k x) n = 0
  exact DirectSum.of_eq_of_ne (β := fun j => ((M.piece j).val.obj U : Type w)) k n x (by omega)

/-- Two sections of the total module with the same homogeneous components in every degree are
equal. -/
theorem totalFun_ext {t t' : M.toPresheafGradedModule.Total U}
    (h : ∀ n, totalFun M U t n = totalFun M U t' n) : t = t' :=
  DFinsupp.ext (fun n => h n)

variable (M U)

/-- **Taking the degree-`n` component of a section of the total module**, as an additive map. -/
def totalFunHom (n : ℤ) :
    M.toPresheafGradedModule.Total U →+ ((M.piece n).val.obj U) where
  toFun t := totalFun M U t n
  map_zero' := totalFun_zero n
  map_add' t t' := totalFun_add t t' n

/-- `totalFunHom M U n` sends a section `t` to its degree-`n` component `totalFun M U t n`. -/
@[simp]
theorem totalFunHom_apply (n : ℤ) (t : M.toPresheafGradedModule.Total U) :
    totalFunHom M U n t = totalFun M U t n := rfl

end Component

variable {M N : GradedModule.{w, w, w} A} (f : M ⟶ N)

/-- **The degreewise assembly of a homomorphism of graded modules on homogeneous sections**, as
an additive map of the total modules. -/
noncomputable def totalAddHom (U : Cᵒᵖ) :
    M.toPresheafGradedModule.Total U →+ N.toPresheafGradedModule.Total U :=
  DirectSum.toAddMonoid fun n =>
    AddMonoidHom.mk'
      (fun x : (M.piece n).val.obj U =>
        N.toPresheafGradedModule.incl n ((f.app n).val.app U x))
      fun x y => by rw [map_add, Stacks.GradedModule.incl_add]

/-- On the inclusion of a degree-`n` section `x`, the assembled map is the inclusion of the image
of `x` under the degree-`n` component of `f`. -/
@[simp]
theorem totalAddHom_incl (U : Cᵒᵖ) (n : ℤ) (x : (M.piece n).val.obj U) :
    totalAddHom f U (M.toPresheafGradedModule.incl n x)
      = N.toPresheafGradedModule.incl n ((f.app n).val.app U x) :=
  by
  unfold totalAddHom
  exact DirectSum.toAddMonoid_of (β := fun k => (M.piece k).val.obj U) _ n x

/-- **The assembled map acts componentwise**: the degree-`n` component of the image is the
image of the degree-`n` component. -/
theorem totalFun_totalAddHom (U : Cᵒᵖ) (t : M.toPresheafGradedModule.Total U) (n : ℤ) :
    totalFun N U (totalAddHom f U t) n = (f.app n).val.app U (totalFun M U t n) := by
  induction t using Stacks.GradedModule.incl_induction with
  | zero => rw [map_zero, totalFun_zero, totalFun_zero, map_zero]
  | incl k x =>
    rcases eq_or_ne k n with rfl | hk
    · rw [totalAddHom_incl, totalFun_incl, totalFun_incl]
    · rw [totalAddHom_incl, totalFun_incl_of_ne hk, totalFun_incl_of_ne hk, map_zero]
  | add t t' ht ht' =>
    rw [map_add, totalFun_add, totalFun_add, ht, ht', map_add]

/-- **The assembled map is injective** as soon as the homomorphism is injective on the sections
of every homogeneous piece: a section of the total module is determined by its components. -/
theorem injective_totalAddHom (U : Cᵒᵖ)
    (h : ∀ n : ℤ, Function.Injective ((f.app n).val.app U)) :
    Function.Injective (totalAddHom f U) := fun t t' htt' =>
  totalFun_ext fun n =>
    h n (((totalFun_totalAddHom f U t n).symm.trans
      (congrArg (fun z => totalFun N U z n) htt')).trans (totalFun_totalAddHom f U t' n))

variable [A.IsCommutative]

/-- The assembled map is compatible with the action of the sections of the total algebra. -/
theorem totalAddHom_smul (U : Cᵒᵖ) (a : A.toPresheafGradedAlgebra.Total U)
    (t : M.toPresheafGradedModule.Total U) :
    totalAddHom f U (a • t) = a • totalAddHom f U t := by
  induction a using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i y =>
    induction t using Stacks.GradedModule.incl_induction with
    | zero => simp
    | incl n x =>
      rw [Stacks.GradedModule.incl_smul_incl, totalAddHom_incl, totalAddHom_incl,
        Stacks.GradedModule.incl_smul_incl]
      exact congrArg (N.toPresheafGradedModule.incl (n + i)) (f.map_smul n i U x y)
    | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]
  | add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]

/-- **The degreewise assembly of a homomorphism of graded modules on homogeneous sections**, as
a linear map over the ring of homogeneous sections of the algebra. -/
noncomputable def totalLinearMap (U : Cᵒᵖ) :
    M.toPresheafGradedModule.Total U →ₗ[A.toPresheafGradedAlgebra.Total U]
      N.toPresheafGradedModule.Total U where
  toFun := totalAddHom f U
  map_add' := map_add (totalAddHom f U)
  map_smul' := totalAddHom_smul f U

/-- The linear map `totalLinearMap f U` agrees with the additive map `totalAddHom f U`. -/
@[simp]
theorem totalLinearMap_apply (U : Cᵒᵖ) (t : M.toPresheafGradedModule.Total U) :
    totalLinearMap f U t = totalAddHom f U t := rfl

end SheafOfModules.GradedModule

end
