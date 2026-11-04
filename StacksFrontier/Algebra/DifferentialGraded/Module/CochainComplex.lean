module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# The cochain complex underlying a differential graded module

A right differential graded module `M` over a differential graded algebra `(A, d)` over a
commutative ring `R` is in particular a cochain complex of `R`-modules: its degree-`n` term is
the homogeneous component `M^n` and its differential is the restriction of `d`. This file
constructs that cochain complex, the cochain map underlying a homomorphism of differential
graded modules, and the resulting additive forgetful functor
`Mod_{(A,d)} ⥤ CochainComplex (ModuleCat R) ℤ`.

## Main definitions

* `DifferentialGradedModule.gradedDifferential`: the differential restricted to a homogeneous
  component, as a map `M^n →ₗ[R] M^{n+1}`.
* `DifferentialGradedModule.toCochainComplex`: the underlying cochain complex of `R`-modules.
* `DifferentialGradedModule.Hom.gradedMap`: a homomorphism restricted to a homogeneous
  component.
* `DifferentialGradedModule.Hom.toCochainMap`: the underlying cochain map of a homomorphism.
* `DifferentialGradedModule.forgetToCochainComplex`: the additive functor forgetting the right
  action.

## Main results

* `DifferentialGradedModule.leibniz_apply`: the Leibniz rule holds for an arbitrary, not
  necessarily homogeneous, element of the algebra.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
-/

@[expose] public section

open CategoryTheory

universe u v w w'

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- The Leibniz rule with no homogeneity assumption on the algebra element: for `x` homogeneous
of degree `n` and arbitrary `a : A`, `d (x a) = (d x) a + (-1)^n • (x (d a))`. -/
theorem leibniz_apply (M : DifferentialGradedModule.{u, v, w} A)
    (n : ℤ) (x : M.M) (hx : x ∈ M.grading n) (a : A.A) :
    M.d (MulOpposite.op a • x) = MulOpposite.op a • M.d x +
      (n.negOnePow : ℤ) • (MulOpposite.op (A.d a) • x) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | homogeneous a => exact M.leibniz n _ x a hx a.property
  | add a b ha hb => simp [add_smul, map_add, ha, hb, smul_add, add_add_add_comm]

/-- The differential restricted to the homogeneous component of degree `n`. -/
def gradedDifferential (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    M.grading n →ₗ[R] M.grading (n + 1) where
  toFun x := ⟨M.d x, M.d_mem n x x.property⟩
  map_add' x y := Subtype.ext (M.d.map_add (x : M.M) (y : M.M))
  map_smul' r x := Subtype.ext (M.d.map_smul r (x : M.M))

/-- `gradedDifferential` is the differential on underlying elements. -/
@[simp] theorem gradedDifferential_apply (M : DifferentialGradedModule.{u, v, w} A)
    (n : ℤ) (x : M.grading n) : (M.gradedDifferential n x : M.M) = M.d x := rfl

/-- The cochain complex of `R`-modules underlying a differential graded module: its degree-`n`
term is `M^n` and its differential is `gradedDifferential`. -/
def toCochainComplex (M : DifferentialGradedModule.{u, v, w} A) :
    CochainComplex (ModuleCat.{w} R) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (M.grading n))
    (fun n ↦ ModuleCat.ofHom (M.gradedDifferential n)) (fun n ↦ by
      ext x; exact LinearMap.congr_fun M.d_comp_d x)

/-- The degree-`n` term of `toCochainComplex` is the homogeneous component `M^n`. -/
@[simp] theorem toCochainComplex_X (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    M.toCochainComplex.X n = ModuleCat.of R (M.grading n) := rfl

/-- The differential of `toCochainComplex` from degree `n` to degree `n + 1` is
`gradedDifferential`. -/
@[simp] theorem toCochainComplex_d (M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    M.toCochainComplex.d n (n + 1) = ModuleCat.ofHom (M.gradedDifferential n) := by
  simp [toCochainComplex]

/-- A homomorphism of differential graded modules restricted to a homogeneous component. -/
def Hom.gradedMap {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f : Hom M N) (n : ℤ) :
    M.grading n →ₗ[R] N.grading n where
  toFun x := ⟨f.toFun x, f.map_grading n x x.property⟩
  map_add' x y := Subtype.ext (f.toFun.map_add (x : M.M) (y : M.M))
  map_smul' r x := Subtype.ext (f.toFun.map_smul r (x : M.M))

/-- `Hom.gradedMap` is the homomorphism on underlying elements. -/
@[simp] theorem Hom.gradedMap_apply {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A}
    (f : Hom M N) (n : ℤ) (x : M.grading n) :
    (f.gradedMap n x : N.M) = f.toFun x := rfl

/-- The cochain map underlying a homomorphism of differential graded modules. -/
def Hom.toCochainMap {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    M.toCochainComplex ⟶ N.toCochainComplex :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (f.gradedMap n)) (fun n ↦ by
    simp only [toCochainComplex_d]
    ext x; apply Subtype.ext
    exact (LinearMap.congr_fun f.map_d (x : M.grading n).val).symm)

/-- The degree-`n` component of `Hom.toCochainMap` is `Hom.gradedMap`. -/
@[simp] theorem Hom.toCochainMap_f {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N) (n : ℤ) :
    f.toCochainMap.f n = ModuleCat.ofHom (f.gradedMap n) := rfl

/-- The forgetful functor from differential graded `A`-modules to cochain complexes of modules
over the base ring. -/
@[implicit_reducible]
def forgetToCochainComplex (A : DifferentialGradedAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v, w} A ⥤ CochainComplex (ModuleCat.{w} R) ℤ where
  obj M := M.toCochainComplex
  map f := f.toCochainMap
  map_id M := by ext n x; rfl
  map_comp f g := by ext n x; rfl

/-- The forgetful functor to cochain complexes is additive. -/
instance (A : DifferentialGradedAlgebra.{u, v} R) :
    (forgetToCochainComplex.{u, v, w} A).Additive where
  map_add := by intros; ext n x; rfl

end DifferentialGradedModule

add_to_stacks 09JI "differential graded modules" DifferentialGradedModule
add_to_stacks 09JI "homomorphisms" DifferentialGradedModule.Hom
add_to_stacks 09JI "the category" DifferentialGradedModule.instCategory
