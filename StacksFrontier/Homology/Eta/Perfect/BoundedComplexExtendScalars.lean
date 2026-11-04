module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a bounded complex of finite free modules, and extension of scalars

A bounded complex of finite free modules given in chosen bases is recorded as a
`BoundedComplex`, whose base change along a ring map `φ : A ⟶ B` is the complex of matrices with
entries the images of the original entries. Extension of scalars, on the other hand, sends the
associated complex of modules to `B ⊗_A -` of it. The two agree: in each degree the canonical
map `B ⊗_A (Fin r → A) ⟶ (Fin r → B)` is an isomorphism, and it carries the extension of
scalars of a matrix differential to the differential of the base-changed matrix.

## Main definitions

* `BoundedComplex.extendScalarsTermIso`: the degreewise comparison.
* `BoundedComplex.extendScalarsIso`: the comparison of complexes.

## Main results

* `piScalarRight_mulVec`: extension of scalars of multiplication by a matrix is multiplication
  by the matrix of images, under the canonical identification of a base-changed finite free
  module with a finite free module.

## Implementation notes

Everything here is stated at the level of a ring map and finite index types, so that no scheme
term ever appears; consumers on schemes instantiate it at a ring of sections. The ring map is
turned into an algebra structure where needed, which is the structure extension of scalars uses
as well, so the two tensor products agree without transport.

## References

* [Stacks Project, Tag 0GSU](https://stacks.math.columbia.edu/tag/0GSU)
* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-- Extension of scalars of multiplication by a matrix is multiplication by the matrix of
images: the canonical identification of `B ⊗_A (ι → A)` with `ι → B` intertwines the two. -/
public theorem piScalarRight_mulVec {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (d : Matrix κ ι A) :
    (TensorProduct.piScalarRight A B B κ).toLinearMap.comp (d.mulVecLin.baseChange B) =
      (d.map (algebraMap A B)).mulVecLin.comp
        (TensorProduct.piScalarRight A B B ι).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  funext j
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Algebra.smul_def,
    map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

section

variable {A B : Type u} [CommRing A] [CommRing B]

/-- In each degree, extension of scalars of the complex of a bounded matrix complex is the
degree of the complex of the base-changed matrix complex. -/
public def BoundedComplex.extendScalarsTermIso (φ : A →+* B) (C : BoundedComplex A) (i : ℤ) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C.toCochainComplex).X i ≅ (C.baseChange φ).toCochainComplex.X i :=
  let : Algebra A B := φ.toAlgebra
  (TensorProduct.piScalarRight A B B (Fin (C.rank i))).toModuleIso

/-- Extension of scalars along `φ` carries the complex of a bounded matrix complex to the
complex of its base change along `φ`. -/
public def BoundedComplex.extendScalarsIso (φ : A →+* B) (C : BoundedComplex A) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C.toCochainComplex ≅ (C.baseChange φ).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (C.extendScalarsTermIso φ) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    let : Algebra A B := φ.toAlgebra
    simp only [BoundedComplex.extendScalarsTermIso, Functor.mapHomologicalComplex_obj_d,
      BoundedComplex.toCochainComplex_d, LinearEquiv.toModuleIso_hom]
    exact ModuleCat.hom_ext (piScalarRight_mulVec (C.d i)).symm)

end

end
