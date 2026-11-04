module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryAdditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Quotient.Linear

/-!
# Differential graded modules over a sheaf of algebras over a constant ring are linear

Let `R` be a commutative ring and let `(A, d)` be a sheaf of differential graded algebras over
the constant sheaf of rings with value `R` on a site with the chaotic topology. Multiplication by
`r ∈ R` is an endomorphism of every right differential graded `A`-module: it is multiplication by
the constant global section `r` on each homogeneous piece, it commutes with the differential
because the differential is `O`-linear, and with the action of `A` because that action is
`O`-bilinear. These endomorphisms are natural and form a ring homomorphism into the centre of the
category, so the category of right differential graded `A`-modules, and its homotopy category,
are `R`-linear categories. This is the `R`-linear structure of `D(A, d)` in Remark 0H1E.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.constScalar`: the constant global section `r`.
* `SheafOfModules.DifferentialGradedModule.scalarEnd`: multiplication by `r` on a right
  differential graded `A`-module.
* `SheafOfModules.DifferentialGradedModule.scalarCenter`: the ring homomorphism from `R` into the
  centre of the category of right differential graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.instLinear`: the `R`-linear structure on the category
  of right differential graded `A`-modules.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instLinear`: the `R`-linear
  structure on the homotopy category, for which the quotient functor is `R`-linear.

## References

* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v a m

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type v} [Category.{v} C] {R : Type u} [CommRing R]
  {A : DifferentialGradedAlgebra.{u, a} (Stacks.PresheafOfModules.constRingSheaf (C := C) R)}

/-- The sections of the constant sheaf of rings with value `R` are commutative. -/
instance constRingSheaf_isMulCommutative (U : Cᵒᵖ) :
    IsMulCommutative ((Stacks.PresheafOfModules.constRingSheaf (C := C) R).obj.obj U) :=
  inferInstanceAs (IsMulCommutative R)

/-- The constant global section `r` of the constant sheaf of rings with value `R`. -/
def constScalar (r : R) :
    ((Stacks.PresheafOfModules.constRingSheaf (C := C) R).obj ⋙
      CategoryTheory.forget RingCat).sections :=
  ⟨fun _ => r, fun _ => rfl⟩

/-- **Multiplication by `r ∈ R` on a right differential graded `A`-module**: multiplication by the
constant global section `r` on every homogeneous piece. -/
def scalarEnd (r : R) (M : DifferentialGradedModule.{u, a, m} A) : M ⟶ M where
  toHomologicalComplex :=
    { f := fun n => (Stacks.SheafOfModules.globalSectionToEnd _ (constScalar r)).app (M.complex.X n)
      comm' := fun _ _ _ =>
        ((Stacks.SheafOfModules.globalSectionToEnd _ (constScalar r)).naturality _).symm }
  map_mul n i U x y := ((M.mul n i).map_smul_left U ((constScalar r).val U) x y).symm

/-- On sections over `U`, the `n`-th component of `scalarEnd r M` is multiplication by the
constant section `r`. -/
@[simp]
theorem scalarEnd_apply (r : R) (M : DifferentialGradedModule.{u, a, m} A) (n : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) :
    ((scalarEnd r M).toHomologicalComplex.f n).val.app U x = (constScalar r).val U • x :=
  rfl

/-- **Multiplication by elements of `R`, as a ring homomorphism into the centre of the category of
right differential graded `A`-modules.** -/
def scalarCenter : R →+* CatCenter (DifferentialGradedModule.{u, a, m} A) where
  toFun r :=
    { app := scalarEnd r
      naturality := fun _ _ g => Hom.ext fun n => by
        ext U x
        exact (((g.toHomologicalComplex.f n).val.app U).hom.map_smul ((constScalar r).val U)
          x).symm }
  map_one' := NatTrans.ext <| funext fun M => Hom.ext fun n => by
    ext U x
    exact one_smul ((Stacks.PresheafOfModules.constRingSheaf (C := C) R).obj.obj U) x
  map_mul' r s := NatTrans.ext <| funext fun M => Hom.ext fun n => by
    ext U x
    change (constScalar (r * s)).val U • x = (constScalar r).val U • (constScalar s).val U • x
    rw [← mul_smul]
    rfl
  map_zero' := NatTrans.ext <| funext fun M => Hom.ext fun n => by
    ext U x
    exact zero_smul ((Stacks.PresheafOfModules.constRingSheaf (C := C) R).obj.obj U) x
  map_add' r s := NatTrans.ext <| funext fun M => Hom.ext fun n => by
    ext U x
    exact add_smul ((constScalar r).val U) ((constScalar s).val U) x

/-- **The category of right differential graded `A`-modules is `R`-linear**, the scalar `r`
acting by `scalarEnd r`. -/
@[instance_reducible]
instance instLinear : Linear R (DifferentialGradedModule.{u, a, m} A) :=
  Linear.ofRingMorphism scalarCenter

/-- Scalar multiplication of morphisms is precomposition with `scalarEnd`. -/
theorem smul_eq_scalarEnd_comp (r : R) {M N : DifferentialGradedModule.{u, a, m} A}
    (f : M ⟶ N) : r • f = scalarEnd r M ≫ f :=
  Linear.smulOfRingMorphism_smul_eq scalarCenter r f

/-- **The homotopy category of right differential graded `A`-modules is `R`-linear**, and the
quotient functor is `R`-linear: homotopic morphisms stay homotopic after scaling. -/
@[instance_reducible]
instance HomotopyCategory.instLinear : Linear R (HomotopyCategory.{u, a, m} A) :=
  haveI : (CategoryTheory.Quotient.functor
      (fun {M N : DifferentialGradedModule.{u, a, m} A} (f g : M ⟶ N) => Homotopic f g)).Additive :=
    inferInstanceAs (HomotopyCategory.quotient.{u, a, m} A).Additive
  CategoryTheory.Quotient.linear R
    (fun {M N : DifferentialGradedModule.{u, a, m} A} (f g : M ⟶ N) => Homotopic f g)
    (fun r _ _ f₁ f₂ h => by
      rw [smul_eq_scalarEnd_comp, smul_eq_scalarEnd_comp]
      exact (homotopic_congruence A).comp_left _ h)

/-- The quotient functor onto the homotopy category is `R`-linear. -/
instance HomotopyCategory.quotient_linear :
    Functor.Linear R (HomotopyCategory.quotient.{u, a, m} A) :=
  haveI : (CategoryTheory.Quotient.functor
      (fun {M N : DifferentialGradedModule.{u, a, m} A} (f g : M ⟶ N) => Homotopic f g)).Additive :=
    inferInstanceAs (HomotopyCategory.quotient.{u, a, m} A).Additive
  CategoryTheory.Quotient.linear_functor R
    (fun {M N : DifferentialGradedModule.{u, a, m} A} (f g : M ⟶ N) => Homotopic f g) _

end SheafOfModules.DifferentialGradedModule
