module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule

/-!
# Restriction of graded algebras and graded modules to a slice site

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` be a sheaf of `ℤ`-graded `R`-algebras
and let `U` be an object of `C`. Writing `j : Sh(C/U) ⟶ Sh(C)` for the localization morphism,
this file constructs the restriction `A_U = j^*A` of `A` to the slice site, and the restriction
`j^*` of right and of left graded `A`-modules to graded `A_U`-modules.

## Main definitions

* `SheafOfModules.GradedAlgebra.over` is the restricted sheaf of graded algebras `A_U`, whose
  homogeneous pieces are the restrictions `A^n|_U` of those of `A`.
* `SheafOfModules.GradedModule.over` and `SheafOfModules.LeftGradedModule.over` restrict a
  right, respectively left, graded `A`-module to a graded `A_U`-module, with
  `SheafOfModules.GradedModule.overMap` and `SheafOfModules.LeftGradedModule.overMap` on
  homomorphisms and `SheafOfModules.GradedModule.overFunctor`,
  `SheafOfModules.LeftGradedModule.overFunctor` the resulting functors `j^*`.

## Main results

* `SheafOfModules.GradedAlgebra.over_piece`, `SheafOfModules.GradedModule.over_smul` and their
  companions: the homogeneous pieces, the multiplication and the actions of the restricted
  objects are those of the original read on the objects of the slice site, definitionally.

## References

* [Stacks Project, Tag 0FR9](https://stacks.math.columbia.edu/tag/0FR9)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The restriction `A_U = j^*A` of a sheaf of graded algebras to the slice site at `U`: its
homogeneous pieces are the restrictions of those of `A`, and its multiplication and unit are
those of `A` read on the objects of the slice site. -/
noncomputable def GradedAlgebra.over (A : GradedAlgebra.{t, a} R) (U : C) :
    GradedAlgebra.{t, a} (R.over U) where
  piece n := (A.piece n).over U
  mul i j :=
    { app V := (A.mul i j).app (op V.unop.left)
      map_smul_left V r x y := (A.mul i j).map_smul_left (op V.unop.left) r x y
      map_smul_right V r x y := (A.mul i j).map_smul_right (op V.unop.left) r x y
      naturality f x y := (A.mul i j).naturality f.unop.left.op x y }
  one := ⟨fun V => A.one.eval (op V.unop.left), fun f => A.one.property f.unop.left.op⟩
  mul_assoc i j k V := A.mul_assoc i j k (op V.unop.left)
  one_mul i V := A.one_mul i (op V.unop.left)
  mul_one i V := A.mul_one i (op V.unop.left)

/-- The homogeneous pieces of `A_U` are the restrictions of those of `A`. -/
@[simp]
theorem GradedAlgebra.over_piece (A : GradedAlgebra.{t, a} R) (U : C) (n : ℤ) :
    (A.over U).piece n = (A.piece n).over U := rfl

/-- The multiplication of `A_U` at `V` is that of `A` at the underlying object of `V`. -/
@[simp]
theorem GradedAlgebra.over_mul_app (A : GradedAlgebra.{t, a} R) (U : C) (i j : ℤ)
    (V : (Over U)ᵒᵖ) : ((A.over U).mul i j).app V = (A.mul i j).app (op V.unop.left) := rfl

/-- The unit of `A_U` at `V` is that of `A` at the underlying object of `V`. -/
@[simp]
theorem GradedAlgebra.over_one_eval (A : GradedAlgebra.{t, a} R) (U : C) (V : (Over U)ᵒᵖ) :
    (A.over U).one.eval V = A.one.eval (op V.unop.left) := rfl

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- The restriction `j^*M` of a right graded `A`-module to a right graded `A_U`-module. -/
noncomputable def over (M : GradedModule.{t, a, m} A) (U : C) :
    GradedModule.{t, a, m} (A.over U) where
  piece n := (M.piece n).over U
  smul n i V := M.smul n i (op V.unop.left)
  smul_smul_left n i V r x y := M.smul_smul_left n i (op V.unop.left) r x y
  smul_smul_right n i V r x y := M.smul_smul_right n i (op V.unop.left) r x y
  smul_naturality := fun n i {_ _} f x y => M.smul_naturality n i f.unop.left.op x y
  smul_mul n i j V := M.smul_mul n i j (op V.unop.left)
  smul_one n V := M.smul_one n (op V.unop.left)

/-- The homogeneous pieces of `j^*M` are the restrictions of those of `M`. -/
@[simp]
theorem over_piece (M : GradedModule.{t, a, m} A) (U : C) (n : ℤ) :
    (M.over U).piece n = (M.piece n).over U := rfl

/-- The action on `j^*M` at `V` is that of `M` at the underlying object of `V`. -/
@[simp]
theorem over_smul (M : GradedModule.{t, a, m} A) (U : C) (n i : ℤ) (V : (Over U)ᵒᵖ) :
    (M.over U).smul n i V = M.smul n i (op V.unop.left) := rfl

/-- The restriction of a homomorphism of right graded modules to the slice site at `U`. -/
noncomputable def overMap {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) (U : C) :
    M.over U ⟶ N.over U where
  app n := (f.app n).over U
  map_smul n i V x y := f.map_smul n i (op V.unop.left) x y

/-- The components of the restricted homomorphism are the restrictions of those of `f`. -/
@[simp]
theorem overMap_app {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) (U : C) (n : ℤ) :
    (overMap f U).app n = (f.app n).over U := rfl

/-- The restriction functor `j^* : Mod^gr(A) ⥤ Mod^gr(A_U)` on right graded modules. -/
noncomputable def overFunctor (A : GradedAlgebra.{t, a} R) (U : C) :
    GradedModule.{t, a, m} A ⥤ GradedModule.{t, a, m} (A.over U) where
  obj M := M.over U
  map f := overMap f U
  map_id _ := Hom.ext fun _ => (SheafOfModules.overFunctor R U).map_id _
  map_comp _ _ := Hom.ext fun _ => (SheafOfModules.overFunctor R U).map_comp _ _

/-- The restriction functor sends `M` to `j^*M`. -/
@[simp]
theorem overFunctor_obj (A : GradedAlgebra.{t, a} R) (U : C) (M : GradedModule.{t, a, m} A) :
    (overFunctor A U).obj M = M.over U := rfl

/-- The restriction functor restricts each component of a homomorphism. -/
@[simp]
theorem overFunctor_map_app (A : GradedAlgebra.{t, a} R) (U : C)
    {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    ((overFunctor A U).map f).app n = (f.app n).over U := rfl

end GradedModule

namespace LeftGradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- The restriction `N|_U` of a left graded `A`-module to a left graded `A_U`-module. -/
noncomputable def over (N : LeftGradedModule.{t, a, m} A) (U : C) :
    LeftGradedModule.{t, a, m} (A.over U) where
  piece n := (N.piece n).over U
  smul i n V := N.smul i n (op V.unop.left)
  smul_smul_left i n V r a x := N.smul_smul_left i n (op V.unop.left) r a x
  smul_smul_right i n V r a x := N.smul_smul_right i n (op V.unop.left) r a x
  smul_naturality := fun i n {_ _} f a x => N.smul_naturality i n f.unop.left.op a x
  mul_smul i j n V := N.mul_smul i j n (op V.unop.left)
  one_smul n V := N.one_smul n (op V.unop.left)

/-- The homogeneous pieces of `N|_U` are the restrictions of those of `N`. -/
@[simp]
theorem over_piece (N : LeftGradedModule.{t, a, m} A) (U : C) (n : ℤ) :
    (N.over U).piece n = (N.piece n).over U := rfl

/-- The action on `N|_U` at `V` is that of `N` at the underlying object of `V`. -/
@[simp]
theorem over_smul (N : LeftGradedModule.{t, a, m} A) (U : C) (i n : ℤ) (V : (Over U)ᵒᵖ) :
    (N.over U).smul i n V = N.smul i n (op V.unop.left) := rfl

/-- The restriction of a homomorphism of left graded modules to the slice site at `U`. -/
noncomputable def overMap {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) (U : C) :
    M.over U ⟶ N.over U where
  app n := (f.app n).over U
  map_smul i n V a x := f.map_smul i n (op V.unop.left) a x

/-- The components of the restricted homomorphism are the restrictions of those of `f`. -/
@[simp]
theorem overMap_app {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) (U : C) (n : ℤ) :
    (overMap f U).app n = (f.app n).over U := rfl

/-- The restriction functor `j^*` on left graded modules. -/
noncomputable def overFunctor (A : GradedAlgebra.{t, a} R) (U : C) :
    LeftGradedModule.{t, a, m} A ⥤ LeftGradedModule.{t, a, m} (A.over U) where
  obj N := N.over U
  map f := overMap f U
  map_id _ := Hom.ext fun _ => (SheafOfModules.overFunctor R U).map_id _
  map_comp _ _ := Hom.ext fun _ => (SheafOfModules.overFunctor R U).map_comp _ _

/-- The restriction functor sends `N` to `N|_U`. -/
@[simp]
theorem overFunctor_obj (A : GradedAlgebra.{t, a} R) (U : C)
    (N : LeftGradedModule.{t, a, m} A) : (overFunctor A U).obj N = N.over U := rfl

/-- The restriction functor restricts each component of a homomorphism. -/
@[simp]
theorem overFunctor_map_app (A : GradedAlgebra.{t, a} R) (U : C)
    {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    ((overFunctor A U).map f).app n = (f.app n).over U := rfl

end LeftGradedModule

end SheafOfModules

end
