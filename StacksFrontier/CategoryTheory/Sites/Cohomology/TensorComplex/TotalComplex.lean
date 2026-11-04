module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.MonoidalStructureOnPresheaves
import StacksCore.Tactic.StacksAttribute

/-! # The total tensor-product complex of complexes of modules on a ringed site

Let `(C, O)` be a ringed site. The tensor product of two sheaves of `O`-modules is the
sheafification of the presheaf `U ↦ A(U) ⊗_{O(U)} B(U)`, and for complexes `A` and `B` of
`O`-modules the *total* tensor-product complex is formed by taking the total complex of the
double complex of presheaf tensor products and sheafifying it degreewise. This file records
that complex, `AlgebraicGeometry.RingedSite.tensorTotal`, together with its functoriality and
with the homogeneous local pure tensors `a ⊗ b` that generate it, and the universal property
of the degreewise sheafification that lets a morphism out of it be defined on the presheaf
level.

This is the tensor complex in which the evaluation map of Stacks 0A92 and the composition map
of Stacks 0A91 have their source. It takes the total complex first and sheafifies afterwards,
which is what makes the pure tensors `tensorTotalSection` available; the degreewise
sheafification is exact, so this agrees with `Stacks.SheafOfModules.Tensor.tensorComplex`, which
sheafifies first and totalises afterwards.

## Main definitions

* `AlgebraicGeometry.RingedSite.underlyingPresheafComplex`: the underlying complex of
  presheaves of modules of a complex of sheaves of modules.
* `AlgebraicGeometry.RingedSite.tensorTotalPresheaf`, with its summands
  `AlgebraicGeometry.RingedSite.tensorTotalPresheafTerm` and their inclusions
  `AlgebraicGeometry.RingedSite.ιTensorTotalPresheaf`: the presheaf-level total complex whose
  degreewise sheafification is the total tensor-product complex.
* `AlgebraicGeometry.RingedSite.tensorTotal` and
  `AlgebraicGeometry.RingedSite.tensorTotalMap`: the total tensor-product complex and its
  functoriality in both arguments.
* `AlgebraicGeometry.RingedSite.tensorTotalSection`: the homogeneous local pure tensor of a
  section of `A` of degree `t` and a section of `B` of degree `r`.
* `AlgebraicGeometry.RingedSite.sheafifyLift`: a morphism of complexes out of the total tensor
  product, from a morphism of complexes of presheaves of modules out of the presheaf-level
  total complex.

## Implementation notes

The monoidal structure on presheaves of modules is over the presheaf of *commutative* rings
`O`, and the bifunctor `curriedTensor` and its partial applications preserve zero morphisms,
which is what makes the total complex of the double complex of tensor products available.
Those instances live in `StacksDraft.Ch21.Sec34.RingedSiteMonoidalInstances` and are switched
on file-locally below; they are deliberately not global, since the `CommRing` structure on the
sections of `X.ringSheaf` is a second route to the `Ring` structure that `RingCat` already
carries.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- The forgetful functor from sheaves of modules to presheaves of modules preserves zero
morphisms. -/
local instance : (SheafOfModules.forget.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The underlying complex of presheaves of modules of a complex of sheaves of modules. -/
noncomputable abbrev underlyingPresheafComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  ((SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The presheaf-level total tensor-product complex: the total complex of the double complex of
pointwise tensor products of the underlying presheaves of modules. Its degreewise
sheafification is `AlgebraicGeometry.RingedSite.tensorTotal`. -/
noncomputable abbrev tensorTotalPresheaf
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ :=
  HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A) (underlyingPresheafComplex X B)
    (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
    (ComplexShape.up ℤ)

/-- The `(t, r)` summand of `AlgebraicGeometry.RingedSite.tensorTotalPresheaf`: the pointwise
tensor product of the underlying presheaves of `A^t` and `B^r`. -/
noncomputable abbrev tensorTotalPresheafTerm
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t r : ℤ) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
  ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
      ((underlyingPresheafComplex X A).X t)).obj ((underlyingPresheafComplex X B).X r)

/-- The inclusion of the `(t, r)` summand into the degree-`c` term of
`AlgebraicGeometry.RingedSite.tensorTotalPresheaf`. -/
noncomputable abbrev ιTensorTotalPresheaf
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (t r c : ℤ) (h : t + r = c) :
    tensorTotalPresheafTerm X A B t r ⟶ (tensorTotalPresheaf X A B).X c :=
  HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A) (underlyingPresheafComplex X B)
    (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
    (ComplexShape.up ℤ) t r c
    (show ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c by
      simpa using h)

/-- The total tensor-product complex of two complexes of sheaves of modules: the total complex
of the double complex of pointwise tensor products of the underlying presheaves, sheafified
degreewise. -/
noncomputable abbrev tensorTotal
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  ((PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (tensorTotalPresheaf X A B)

/-- The morphism of total tensor-product complexes induced by morphisms in both factors. -/
noncomputable abbrev tensorTotalMap
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    tensorTotal X A B ⟶ tensorTotal X A' B' :=
  ((PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (HomologicalComplex.mapBifunctorMap
        (((SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)
        (((SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g)
        (curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ))

/-- The homogeneous local pure tensor in the total tensor-product complex determined by a
section of `A` of degree `t` and a section of `B` of degree `r` over the same object. -/
noncomputable abbrev tensorTotalSection
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    ((tensorTotal X A B).X (t + r)).val.obj (op U) :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
    ((tensorTotalPresheaf X A B).X (t + r))).app (op U))
    ((ιTensorTotalPresheaf X A B t r (t + r) rfl).app (op U)
      (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b))

/-- A morphism of complexes of presheaves of modules into the underlying complex of a complex
of sheaves of modules extends to the degreewise sheafification of its source. -/
noncomputable def sheafifyLift
    {A : CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ}
    {B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ underlyingPresheafComplex X B) :
    ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶ B where
  f n := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv _ _).symm
    (f.f n)
  comm' i j _ :=
    (Adjunction.homEquiv_naturality_right_square
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (A.d i j) (f.f j) (f.f i) (B.d i j) (f.comm i j).symm).symm

/-- `sheafifyLift f` restricts along the sheafification unit to `f`. -/
lemma sheafifyLift_unit
    {A : CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ}
    {B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ underlyingPresheafComplex X B) (n : ℤ) :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app (A.X n) ≫
        ((sheafifyLift X f).f n).val = f.f n :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv _ _).apply_symm_apply
    (f.f n)

/-- `sheafifyLift f` agrees with `f` on sections coming from the presheaf level. -/
lemma sheafifyLift_unit_apply
    {A : CochainComplex (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) ℤ}
    {B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ underlyingPresheafComplex X B) (n : ℤ) (U : X.Cᵒᵖ) (x : (A.X n).obj U) :
    ((sheafifyLift X f).f n).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (A.X n)).app U x) = (f.f n).app U x :=
  congrArg (fun g ↦ g.app U x) (sheafifyLift_unit X f n)

end AlgebraicGeometry.RingedSite

end
