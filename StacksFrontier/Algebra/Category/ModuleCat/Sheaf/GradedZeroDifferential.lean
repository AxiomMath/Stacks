module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward

/-!
# Sheaves of graded algebras and modules as differential graded ones with zero differential

A sheaf of graded algebras `A` is a sheaf of differential graded algebras whose differential is
zero, and a right graded `A`-module is a right differential graded module over it whose
differential is zero: the signed Leibniz rule holds trivially, every term of it being zero.
This file records that reading, together with the matching statements for homomorphisms, so
that constructions made for sheaves of differential graded modules apply to sheaves of graded
modules.

## Main definitions

* `SheafOfModules.zeroDifferentialComplex` is the cochain complex of sheaves of modules with
  given terms and zero differential.
* `SheafOfModules.GradedAlgebra.withZeroDifferential` is a sheaf of graded algebras read as a
  sheaf of differential graded algebras with zero differential, and
  `SheafOfModules.GradedModule.withZeroDifferential` is a right graded module read as a right
  differential graded module with zero differential.
* `SheafOfModules.GradedModule.homWithZeroDifferential` identifies homomorphisms of right graded
  modules with morphisms of the differential graded modules with zero differential.
* `SheafOfModules.GradedModule.SemilinearHom.withZeroDifferential` reads a semilinear
  homomorphism of right graded modules as a semilinear map of the differential graded modules
  with zero differential.

## Implementation notes

The homogeneous pieces, the multiplications and the units of the differential graded objects
are the graded ones on the nose, so the graded algebra underlying
`GradedAlgebra.withZeroDifferential A` is `A` up to the structure eta law, and the graded module
underlying `GradedModule.withZeroDifferential N` is `N` likewise; both identifications hold by
`rfl`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory Limits

universe t a m v u a' v' u'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The cochain complex of sheaves of modules with terms `X n` and zero differential. -/
def zeroDifferentialComplex (X : ℤ → SheafOfModules.{a} R) :
    CochainComplex (SheafOfModules.{a} R) ℤ where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

/-- The terms of the complex with zero differential are the given sheaves of modules. -/
@[simp]
theorem zeroDifferentialComplex_X (X : ℤ → SheafOfModules.{a} R) (n : ℤ) :
    (zeroDifferentialComplex X).X n = X n :=
  rfl

/-- The differential of the complex with zero differential is zero. -/
@[simp]
theorem zeroDifferentialComplex_d (X : ℤ → SheafOfModules.{a} R) (i j : ℤ) :
    (zeroDifferentialComplex X).d i j = 0 :=
  rfl

namespace GradedAlgebra

/-- **A sheaf of graded algebras, read as a sheaf of differential graded algebras with zero
differential.** -/
def withZeroDifferential (A : GradedAlgebra.{t, a} R) : DifferentialGradedAlgebra.{t, a} R where
  complex := zeroDifferentialComplex A.piece
  mul := A.mul
  one := A.one
  mul_assoc := A.mul_assoc
  one_mul := A.one_mul
  mul_one := A.mul_one
  leibniz n i U x y := by
    have h1 : (A.mul (n + 1) i).app U 0 y = 0 :=
      (DFunLike.congr_fun (map_zero ((A.mul (n + 1) i).app U)) y).trans
        (AddMonoidHom.zero_apply y)
    have h2 : (A.mul n (i + 1)).app U x 0 = 0 := map_zero _
    change (0 : (A.piece (n + i + 1)).val.obj U) =
      gradedCast (fun q ↦ (A.piece q).val.obj U) (add_right_comm n 1 i)
          ((A.mul (n + 1) i).app U 0 y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (A.piece q).val.obj U) (add_assoc n i 1).symm
            ((A.mul n (i + 1)).app U x 0)
    rw [h1, h2, gradedCast_zero, gradedCast_zero, smul_zero, add_zero]

/-- The cochain complex of `A` read with zero differential has the homogeneous pieces of `A` as
its terms. -/
@[simp]
theorem withZeroDifferential_complex_X (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    A.withZeroDifferential.complex.X n = A.piece n :=
  rfl

/-- The differential of `A` read with zero differential is zero. -/
@[simp]
theorem withZeroDifferential_complex_d (A : GradedAlgebra.{t, a} R) (i j : ℤ) :
    A.withZeroDifferential.complex.d i j = 0 :=
  rfl

end GradedAlgebra

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- **A right graded `A`-module, read as a right differential graded module with zero
differential** over `A` read with zero differential. -/
def withZeroDifferential (N : GradedModule.{t, a, m} A) :
    DifferentialGradedModule.{t, a, m} A.withZeroDifferential where
  complex := zeroDifferentialComplex N.piece
  mul n i :=
    { app := fun U => N.smul n i U
      map_smul_left := N.smul_smul_left n i
      map_smul_right := N.smul_smul_right n i
      naturality := fun f x y => N.smul_naturality n i f x y }
  mul_assoc := N.smul_mul
  mul_one := N.smul_one
  leibniz n i U x y := by
    have h1 : N.smul (n + 1) i U 0 y = 0 :=
      (DFunLike.congr_fun (map_zero (N.smul (n + 1) i U)) y).trans (AddMonoidHom.zero_apply y)
    have h2 : N.smul n (i + 1) U x 0 = 0 := map_zero _
    change (0 : (N.piece (n + i + 1)).val.obj U) =
      gradedCast (fun q ↦ (N.piece q).val.obj U) (add_right_comm n 1 i)
          (N.smul (n + 1) i U 0 y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (N.piece q).val.obj U) (add_assoc n i 1).symm
            (N.smul n (i + 1) U x 0)
    rw [h1, h2, gradedCast_zero, gradedCast_zero, smul_zero, add_zero]

/-- The graded module underlying `N` read with zero differential is `N`. -/
theorem forgetToGradedModule_obj_withZeroDifferential (N : GradedModule.{t, a, m} A) :
    (forgetToGradedModule A.withZeroDifferential).obj N.withZeroDifferential = N :=
  rfl

/-- A morphism of right differential graded modules out of a module whose differential vanishes
into a module read with zero differential is a homomorphism of the underlying graded modules. -/
def homWithZeroDifferential {X : DifferentialGradedModule.{t, a, m} A.withZeroDifferential}
    (hX : ∀ i j, X.complex.d i j = 0) {N : GradedModule.{t, a, m} A}
    (g : (forgetToGradedModule A.withZeroDifferential).obj X ⟶
      (forgetToGradedModule A.withZeroDifferential).obj N.withZeroDifferential) :
    X ⟶ N.withZeroDifferential where
  toHomologicalComplex :=
    { f := g.app
      comm' := fun i j _ => by
        change g.app i ≫ 0 = X.complex.d i j ≫ g.app j
        rw [hX i j, comp_zero]
        exact zero_comp.symm }
  map_mul := g.map_smul

/-- The homomorphism of graded modules underlying `homWithZeroDifferential hX g` is `g`. -/
@[simp]
theorem forgetToGradedModule_map_homWithZeroDifferential
    {X : DifferentialGradedModule.{t, a, m} A.withZeroDifferential}
    (hX : ∀ i j, X.complex.d i j = 0) {N : GradedModule.{t, a, m} A}
    (g : (forgetToGradedModule A.withZeroDifferential).obj X ⟶
      (forgetToGradedModule A.withZeroDifferential).obj N.withZeroDifferential) :
    (forgetToGradedModule A.withZeroDifferential).map (homWithZeroDifferential hX g) = g :=
  rfl

end GradedModule

namespace GradedModule

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{t}} {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : GradedAlgebra.{t, a} R} {B : GradedAlgebra.{t, a'} R'}
  (φ : DifferentialGradedAlgebra.SemilinearHom u σ B.withZeroDifferential A.withZeroDifferential)

/-- A semilinear homomorphism of right graded modules, read as a semilinear map of the right
differential graded modules with zero differential: commutation with the differentials holds
because both differentials vanish. -/
def SemilinearHom.withZeroDifferential {N : GradedModule.{t, a', m} B}
    {P : GradedModule.{t, a, m} A} (θ : SemilinearHom φ.toGradedAlgebraHom N P) :
    DifferentialGradedModule.SemilinearHom φ N.withZeroDifferential P.withZeroDifferential where
  app := θ.app
  map_smul := θ.map_smul
  naturality := θ.naturality
  comm_d i V x := by
    change θ.app (i + 1) V 0 = 0
    exact map_zero _
  map_mul := θ.map_smul_right

/-- The semilinear homomorphism of right graded modules underlying a semilinear map of right
differential graded modules, obtained by forgetting compatibility with the differentials. -/
def SemilinearHom.ofDifferentialGraded {N : GradedModule.{t, a', m} B}
    {X : DifferentialGradedModule.{t, a, m} A.withZeroDifferential}
    (θ : DifferentialGradedModule.SemilinearHom φ N.withZeroDifferential X) :
    SemilinearHom φ.toGradedAlgebraHom N ((forgetToGradedModule A.withZeroDifferential).obj X)
    where
  app := θ.app
  map_smul := θ.map_smul
  naturality := θ.naturality
  map_smul_right := θ.map_mul

end GradedModule

end SheafOfModules
