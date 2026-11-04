module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of differential graded bimodules: the two one-sided structures, and restriction

Let `R` be a sheaf of rings on a site and let `A` and `B` be sheaves of differential graded
`R`-algebras. A differential graded `(A, B)`-bimodule is the same thing as a right differential
graded `B`-module carrying, in addition, a left differential graded `A`-module structure on the
same complex whose action commutes with the right one. This file makes that reading a
bijection, and then treats the special case produced by a unital homomorphism
`φ : A ⟶ B` of sheaves of differential graded algebras: `B` becomes a differential graded
`(A, B)`-bimodule `{}_A B_B` and every right differential graded `B`-module becomes a right
differential graded `A`-module by restriction along `φ`.

## Main definitions

* `SheafOfModules.DifferentialGradedBimodule.LeftStructure` is a left differential graded
  `A`-module structure on a right differential graded `B`-module which commutes with its right
  action, and `SheafOfModules.DifferentialGradedBimodule.LeftStructure.toLeftModule` is the
  left differential graded `A`-module it makes of the underlying complex.
* `SheafOfModules.DifferentialGradedBimodule.ofLeftStructure` assembles a differential graded
  bimodule out of a right differential graded `B`-module and such a structure, and
  `SheafOfModules.DifferentialGradedBimodule.leftStructure` is the structure a differential
  graded bimodule carries.
* `SheafOfModules.DifferentialGradedBimodule.toRightModuleFunctor` is the functor forgetting
  the left action.
* `SheafOfModules.DifferentialGradedAlgebra.Hom.IsUnital` says that a homomorphism of sheaves of
  differential graded algebras carries the degree-zero unit to the degree-zero unit, and
  `SheafOfModules.DifferentialGradedAlgebra.Hom.comm_d_app` reads its compatibility with the
  differentials on local sections.
* `SheafOfModules.DifferentialGradedAlgebra.asBimodule` is `{}_A B_B`, the sheaf of differential
  graded algebras `B` viewed as a differential graded `(A, B)`-bimodule through a unital
  homomorphism `φ : A ⟶ B`.
* `SheafOfModules.DifferentialGradedModule.restrictScalarsObj` is the right differential graded
  `A`-module obtained from a right differential graded `B`-module by letting a homogeneous
  section `a` of `A` act as `φ a`, and
  `SheafOfModules.DifferentialGradedModule.restrictScalars` is the functor `res_φ` it defines.

## Main results

* `SheafOfModules.DifferentialGradedBimodule.equivLeftStructure`: **a differential graded
  `(A, B)`-bimodule is exactly a right differential graded `B`-module together with a commuting
  left differential graded `A`-module structure.**

## Implementation notes

The right differential graded `B`-module underlying a differential graded `(A, B)`-bimodule is
`SheafOfModules.DifferentialGradedBimodule.toRightModule`; what is added here is the left half
as a separate datum and the inverse construction, which is what turns the reading into a
bijection. The left half is phrased as a structure over a fixed right
differential graded `B`-module rather than as a pair of modules on a common complex, so that no
transport along an equality of complexes appears: the fields of
`SheafOfModules.DifferentialGradedBimodule.LeftStructure` are field-for-field the left-hand
fields of `SheafOfModules.DifferentialGradedBimodule`, and both directions of the bijection are
definitional.

A homomorphism of sheaves of differential graded algebras in this development is a morphism of
complexes respecting the graded multiplication, with no unit condition, so unitality is carried
as the explicit hypothesis `SheafOfModules.DifferentialGradedAlgebra.Hom.IsUnital` wherever the
source's unital homomorphisms are meant. It is exactly what the unit laws of `{}_A B_B` and of
the restriction functor need.

Of the remaining content of the source's section, the tensor-hom adjunction is
`SheafOfModules.isInternalHom_tensor`, and the correspondence between bimodule structures and
homomorphisms into the differential graded endomorphism algebra is
`SheafOfModules.bimoduleStructureEquiv`.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the bimodule
pieces are independent; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedBimodule

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-- A left differential graded `A`-module structure on a right differential graded `B`-module
`M`: a left action of the homogeneous sections of `A` on the complex of `M` which is
associative and unital, obeys the signed Leibniz rule, and commutes with the right action
of `B`. -/
@[sga "6 IV 2.6" "more general"]
structure LeftStructure (A : DifferentialGradedAlgebra.{t, a} R)
    {B : DifferentialGradedAlgebra.{t, a} R} (M : DifferentialGradedModule.{t, a, m} B) where
  /-- Left multiplication by homogeneous sections of `A`. -/
  leftMul (n m : ℤ) : BilinearMap (A.complex.X n) (M.complex.X m) (M.complex.X (n + m))
  /-- The left action is associative. -/
  left_assoc (i j n : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (a' : (A.complex.X j).val.obj U) (x : (M.complex.X n).val.obj U) :
    HEq ((leftMul i (j + n)).app U a ((leftMul j n).app U a' x))
      ((leftMul (i + j) n).app U ((A.mul i j).app U a a') x)
  /-- The left action commutes with the right action of `B`. -/
  left_right_assoc (i n j : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (x : (M.complex.X n).val.obj U) (b : (B.complex.X j).val.obj U) :
    HEq ((M.mul (i + n) j).app U ((leftMul i n).app U a x) b)
      ((leftMul i (n + j)).app U a ((M.mul n j).app U x b))
  /-- The unit of `A` acts as the identity. -/
  one_left (n : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) :
    HEq ((leftMul 0 n).app U (A.one.eval U) x) x
  /-- The left action obeys the signed Leibniz rule. -/
  leibniz_left (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (M.complex.X m).val.obj U) :
    (M.complex.d (n + m) (n + m + 1)).val.app U ((leftMul n m).app U a x) =
      gradedCast (fun q ↦ (M.complex.X q).val.obj U) (add_right_comm n 1 m)
          ((leftMul (n + 1) m).app U ((A.complex.d n (n + 1)).val.app U a) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (M.complex.X q).val.obj U) (add_assoc n m 1).symm
            ((leftMul n (m + 1)).app U a ((M.complex.d m (m + 1)).val.app U x))

/-- The left differential graded `A`-module obtained from a right differential graded
`B`-module with a commuting left `A`-action by forgetting the right action. -/
def LeftStructure.toLeftModule {M : DifferentialGradedModule.{t, a, m} B}
    (S : LeftStructure A M) : LeftDifferentialGradedModule.{t, a, m} A where
  complex := M.complex
  mul := S.leftMul
  mul_assoc n m k U a b x := (S.left_assoc n m k U a b x).symm
  one_mul := S.one_left
  leibniz := S.leibniz_left

/-- The underlying complex of `S.toLeftModule` is that of `M`. -/
@[simp]
theorem LeftStructure.toLeftModule_complex {M : DifferentialGradedModule.{t, a, m} B}
    (S : LeftStructure A M) : S.toLeftModule.complex = M.complex :=
  rfl

/-- The differential graded `(A, B)`-bimodule assembled from a right differential graded
`B`-module and a commuting left differential graded `A`-module structure on it. -/
def ofLeftStructure {M : DifferentialGradedModule.{t, a, m} B} (S : LeftStructure A M) :
    DifferentialGradedBimodule.{t, a, m} A B where
  complex := M.complex
  rightMul := M.mul
  leftMul := S.leftMul
  left_assoc := S.left_assoc
  right_assoc := M.mul_assoc
  left_right_assoc := S.left_right_assoc
  one_left := S.one_left
  one_right := M.mul_one
  leibniz_left := S.leibniz_left
  leibniz_right := M.leibniz

/-- The underlying complex of `ofLeftStructure S` is that of `M`. -/
@[simp]
theorem ofLeftStructure_complex {M : DifferentialGradedModule.{t, a, m} B}
    (S : LeftStructure A M) : (ofLeftStructure S).complex = M.complex :=
  rfl

/-- The commuting left differential graded `A`-module structure that a differential graded
`(A, B)`-bimodule puts on its underlying right differential graded `B`-module. -/
def leftStructure (N : DifferentialGradedBimodule.{t, a, m} A B) :
    LeftStructure A N.toRightModule where
  leftMul := N.leftMul
  left_assoc := N.left_assoc
  left_right_assoc := N.left_right_assoc
  one_left := N.one_left
  leibniz_left := N.leibniz_left

/-- **A differential graded `(A, B)`-bimodule is exactly a right differential graded `B`-module
which is also a left differential graded `A`-module on the same complex, the two actions
commuting.** -/
@[stacks 0FRP "a dg (A,B)-bimodule is a right dg B-module with a commuting left dg A-structure"]
def equivLeftStructure (A B : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedBimodule.{t, a, m} A B ≃
      Σ M : DifferentialGradedModule.{t, a, m} B, LeftStructure A M where
  toFun N := ⟨N.toRightModule, N.leftStructure⟩
  invFun p := ofLeftStructure p.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forgetful functor from differential graded `(A, B)`-bimodules to right differential
graded `B`-modules. -/
def toRightModuleFunctor (A B : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedBimodule.{t, a, m} A B ⥤ DifferentialGradedModule.{t, a, m} B where
  obj N := N.toRightModule
  map f :=
    { toHomologicalComplex := f.toHomologicalComplex
      map_mul := f.map_rightMul }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor sends a bimodule `N` to its underlying right module. -/
@[simp]
theorem toRightModuleFunctor_obj (N : DifferentialGradedBimodule.{t, a, m} A B) :
    (toRightModuleFunctor A B).obj N = N.toRightModule :=
  rfl

/-- In each degree, the image of a morphism `f` under the forgetful functor has the same
component as `f`. -/
@[simp]
theorem toRightModuleFunctor_map_f {N N' : DifferentialGradedBimodule.{t, a, m} A B}
    (f : N ⟶ N') (n : ℤ) :
    ((toRightModuleFunctor A B).map f).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n :=
  rfl

end DifferentialGradedBimodule

namespace DifferentialGradedAlgebra

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-- A homomorphism of sheaves of differential graded algebras is unital when it carries the
degree-zero unit to the degree-zero unit. -/
def Hom.IsUnital (φ : A ⟶ B) : Prop :=
  ∀ U : Cᵒᵖ, (φ.toHomologicalComplex.f 0).val.app U (A.one.eval U) = B.one.eval U

/-- A homomorphism of sheaves of differential graded algebras commutes with the differentials,
read on local sections. -/
theorem Hom.comm_d_app (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) (x : (A.complex.X i).val.obj U) :
    (φ.toHomologicalComplex.f (i + 1)).val.app U ((A.complex.d i (i + 1)).val.app U x) =
      (B.complex.d i (i + 1)).val.app U ((φ.toHomologicalComplex.f i).val.app U x) := by
  have h := homSections_congr (φ.toHomologicalComplex.comm i (i + 1)) U x
  simp only [homSections_apply] at h
  exact h.symm

/-- **`{}_A B_B`: a sheaf of differential graded algebras `B` is a differential graded
`(A, B)`-bimodule** through a unital homomorphism `φ : A ⟶ B`, with `a` acting on the left as
`φ a` and `B` acting on the right by its own multiplication. -/
@[stacks 0FRP "B as a differential graded (A,B)-bimodule through a homomorphism φ : A ⟶ B"]
def asBimodule (φ : A ⟶ B) (hφ : φ.IsUnital) : DifferentialGradedBimodule.{t, a, a} A B where
  complex := B.complex
  rightMul := B.mul
  leftMul n i :=
    { app := fun U => ((B.mul n i).app U).comp (homSections (φ.toHomologicalComplex.f n) U)
      map_smul_left := fun U r x y => by
        change (B.mul n i).app U
            (homSections (φ.toHomologicalComplex.f n) U (r • x)) y = _
        rw [homSections_smul]
        exact (B.mul n i).map_smul_left U r _ y
      map_smul_right := fun U r x y =>
        (B.mul n i).map_smul_right U r _ y
      naturality := fun {U V} f x y => by
        change (B.complex.X (n + i)).val.map f
            ((B.mul n i).app U (homSections (φ.toHomologicalComplex.f n) U x) y) = _
        rw [(B.mul n i).naturality f _ y, homSections_naturality]
        rfl }
  left_assoc i j n U a a' x := by
    have h := B.mul_assoc i j n U ((φ.toHomologicalComplex.f i).val.app U a)
      ((φ.toHomologicalComplex.f j).val.app U a') x
    rw [← φ.map_mul] at h
    exact h.symm
  right_assoc := B.mul_assoc
  left_right_assoc i n j U a x b :=
    B.mul_assoc i n j U ((φ.toHomologicalComplex.f i).val.app U a) x b
  one_left n U x := by
    change HEq ((B.mul 0 n).app U
      ((φ.toHomologicalComplex.f 0).val.app U (A.one.eval U)) x) x
    rw [hφ U]
    exact B.one_mul n U x
  one_right := B.mul_one
  leibniz_left n i U a x := by
    have h := B.leibniz n i U ((φ.toHomologicalComplex.f n).val.app U a) x
    rw [← φ.comm_d_app] at h
    exact h
  leibniz_right := B.leibniz

/-- The underlying complex of the bimodule `asBimodule φ hφ` is that of `B`. -/
@[simp]
theorem asBimodule_complex (φ : A ⟶ B) (hφ : φ.IsUnital) :
    (asBimodule φ hφ).complex = B.complex :=
  rfl

/-- In `asBimodule φ hφ`, a local section `a` of `A` acts on the left on `b` as `φ a * b`. -/
@[simp]
theorem asBimodule_leftMul_app (φ : A ⟶ B) (hφ : φ.IsUnital) (n i : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X n).val.obj U) (b : (B.complex.X i).val.obj U) :
    ((asBimodule φ hφ).leftMul n i).app U a b =
      (B.mul n i).app U ((φ.toHomologicalComplex.f n).val.app U a) b :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-- Restriction of scalars along a unital homomorphism `φ : A ⟶ B` of sheaves of differential
graded algebras: the right differential graded `A`-module on the complex of a right
differential graded `B`-module `M` in which a homogeneous section `a` of `A` acts as `φ a`. -/
@[ega "II 2.8.6" "more general"]
def restrictScalarsObj (φ : A ⟶ B) (hφ : φ.IsUnital)
    (M : DifferentialGradedModule.{t, a, m} B) : DifferentialGradedModule.{t, a, m} A where
  complex := M.complex
  mul n i :=
    { app := fun U =>
        (AddMonoidHom.compHom' (homSections (φ.toHomologicalComplex.f i) U)).comp
          ((M.mul n i).app U)
      map_smul_left := fun U r x y => (M.mul n i).map_smul_left U r x _
      map_smul_right := fun U r x y => by
        change (M.mul n i).app U x
            (homSections (φ.toHomologicalComplex.f i) U (r • y)) = _
        rw [homSections_smul]
        exact (M.mul n i).map_smul_right U r x _
      naturality := fun {U V} f x y => by
        change (M.complex.X (n + i)).val.map f
            ((M.mul n i).app U x (homSections (φ.toHomologicalComplex.f i) U y)) = _
        rw [(M.mul n i).naturality f x _, homSections_naturality]
        rfl }
  mul_assoc n i j U x y z := by
    have h := M.mul_assoc n i j U x ((φ.toHomologicalComplex.f i).val.app U y)
      ((φ.toHomologicalComplex.f j).val.app U z)
    rw [← φ.map_mul] at h
    exact h
  mul_one n U x := by
    change HEq ((M.mul n 0).app U x
      ((φ.toHomologicalComplex.f 0).val.app U (A.one.eval U))) x
    rw [hφ U]
    exact M.mul_one n U x
  leibniz n i U x y := by
    have h := M.leibniz n i U x ((φ.toHomologicalComplex.f i).val.app U y)
    rw [← φ.comm_d_app] at h
    exact h

/-- The underlying complex of `restrictScalarsObj φ hφ M` is that of `M`. -/
@[simp]
theorem restrictScalarsObj_complex (φ : A ⟶ B) (hφ : φ.IsUnital)
    (M : DifferentialGradedModule.{t, a, m} B) :
    (restrictScalarsObj φ hφ M).complex = M.complex :=
  rfl

/-- In `restrictScalarsObj φ hφ M`, a local section `y` of `A` acts on the right on `x` as
`x * φ y`. -/
@[simp]
theorem restrictScalarsObj_mul_app (φ : A ⟶ B) (hφ : φ.IsUnital)
    (M : DifferentialGradedModule.{t, a, m} B) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    ((restrictScalarsObj φ hφ M).mul n i).app U x y =
      (M.mul n i).app U x ((φ.toHomologicalComplex.f i).val.app U y) :=
  rfl

/-- **The restriction functor `res_φ : Mod^dg(B, d) ⥤ Mod^dg(A, d)`** attached to a unital
homomorphism `φ : A ⟶ B` of sheaves of differential graded algebras. -/
@[stacks 0FRP "restriction res_φ along a homomorphism of sheaves of differential graded algebras"]
def restrictScalars (φ : A ⟶ B) (hφ : φ.IsUnital) :
    DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t, a, m} A where
  obj M := restrictScalarsObj φ hφ M
  map f :=
    { toHomologicalComplex := f.toHomologicalComplex
      map_mul := fun n i U x y =>
        f.map_mul n i U x ((φ.toHomologicalComplex.f i).val.app U y) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction functor `restrictScalars φ hφ` sends `M` to `restrictScalarsObj φ hφ M`. -/
@[simp]
theorem restrictScalars_obj (φ : A ⟶ B) (hφ : φ.IsUnital)
    (M : DifferentialGradedModule.{t, a, m} B) :
    (restrictScalars φ hφ).obj M = restrictScalarsObj φ hφ M :=
  rfl

/-- In each degree, the image of a morphism `f` under `restrictScalars φ hφ` has the same
component as `f`. -/
@[simp]
theorem restrictScalars_map_f (φ : A ⟶ B) (hφ : φ.IsUnital)
    {M N : DifferentialGradedModule.{t, a, m} B} (f : M ⟶ N) (n : ℤ) :
    ((restrictScalars φ hφ).map f).toHomologicalComplex.f n = f.toHomologicalComplex.f n :=
  rfl

end DifferentialGradedModule

end SheafOfModules
