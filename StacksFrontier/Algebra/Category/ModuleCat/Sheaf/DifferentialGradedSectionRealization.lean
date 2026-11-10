module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionPinning
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionHomotopy

/-!
# Realizing a presheaf of section modules as a sheaf of differential graded modules

Let `C` be a category with the chaotic topology, let `O` be a sheaf of commutative rings on it
and let `(A, d)` be a sheaf of differential graded `O`-algebras. Over an object `U` the sections
`A(U)` form a differential graded algebra, and over the chaotic topology every presheaf is a
sheaf. So a right differential graded `A`-module is the same thing as a *presheaf of section
modules*: a differential graded `A(U)`-module `X(U)` for every `U`, with homomorphisms
`X(V) ⟶ X(U)_{A(V)}` along the morphisms `V ⟶ U` of `Cᵒᵖ`, read over `A(V)` through the
restriction homomorphism `A(V) ⟶ A(U)`, composing on the nose.

This file turns a presheaf of section modules into a right differential graded `A`-module, the
*realization*. Its degree-`n` piece is the presheaf `U ↦ X(U)ⁿ`, on which a section `r` of `O`
acts through `r · 1 ∈ A⁰(U)`; the right action of a homogeneous section `y` of `A` and the
differential are those of `X(U)`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.sectionScalar`: the ring homomorphism
  `O(U) ⟶ A(U)`, `r ↦ r · 1`, whose image is central.
* `SheafOfModules.DifferentialGradedModule.SectionSystem`: a presheaf of section modules.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.realize`: **its realization**, a right
  differential graded `A`-module.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.realizeFunctor`: the realization as a
  functor, on the category of presheaves of section modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.SectionSystem.sectionsIso`: **the sections of the
  realization over `U` are `X(U)`**, as differential graded `A(U)`-modules.
* `SheafOfModules.DifferentialGradedModule.SectionSystem.sectionModuleRestriction_sectionsIso`
  and `sectionsIso_naturality`: that identification intertwines the restriction maps and is
  natural in `X`.

## References

* [Stacks Project, Section 24.33 (Tag 0GZ8)](https://stacks.math.columbia.edu/tag/0GZ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{t}}

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- The structure map of a direct sum of modules is linear. -/
theorem of_smul (U : Cᵒᵖ) (i : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
    (x : A.toGradedAlgebra.sectionsPiece U i) :
    DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i (r • x) =
      r • DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i x :=
  (DirectSum.lof _ ℤ (A.toGradedAlgebra.sectionsPiece U) i).map_smul r x

/-- **The scalars of `A(U)`**: a section `r` of the sheaf of rings, as the degree-zero section
`r · 1` of `A`. -/
def sectionScalar (U : Cᵒᵖ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U →+*
      A.toGradedAlgebra.totalSections U where
  toFun r := DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (r • A.one.eval U)
  map_one' := by
    rw [one_smul]
    exact DirectSum.of_zero_one _
  map_mul' r s := by
    change DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 ((r * s) • A.one.eval U) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (r • A.one.eval U) *
        DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (s • A.one.eval U)
    rw [GradedAlgebra.of_mul_of_eq, toGradedAlgebra_mul, (A.mul 0 0).map_smul_left,
      (A.mul 0 0).map_smul_right, mul_smul, of_smul, of_smul, of_smul, of_smul,
      SheafOfModules.of_heq (zero_add 0) (A.one_mul 0 U (A.one.eval U))]
  map_zero' := by
    rw [zero_smul]
    exact map_zero _
  map_add' r s := by
    rw [add_smul]
    exact map_add _ _ _

/-- The scalar of `r` is the degree-zero section `r · 1`. -/
theorem sectionScalar_apply (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalar U r = DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (r • A.one.eval U) :=
  rfl

/-- A homogeneous section times the scalar `r · 1` is its scalar multiple. -/
theorem of_mul_sectionScalar (U : Cᵒᵖ) (i : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i p * A.sectionScalar U r =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i (r • p) := by
  rw [sectionScalar_apply, GradedAlgebra.of_mul_of_eq, toGradedAlgebra_mul,
    (A.mul i 0).map_smul_right, of_smul, of_smul,
    SheafOfModules.of_heq (add_zero i) (A.mul_one i U p)]

/-- The scalar `r · 1` times a homogeneous section is its scalar multiple. -/
theorem sectionScalar_mul_of (U : Cᵒᵖ) (i : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalar U r * DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i p =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i (r • p) := by
  rw [sectionScalar_apply, GradedAlgebra.of_mul_of_eq, toGradedAlgebra_mul,
    (A.mul 0 i).map_smul_left, of_smul, of_smul,
    SheafOfModules.of_heq (zero_add i) (A.one_mul i U p)]

/-- **The scalars are central in `A(U)`.** -/
theorem sectionScalar_mul_comm (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
    (x : A.toGradedAlgebra.totalSections U) :
    A.sectionScalar U r * x = x * A.sectionScalar U r := by
  induction x using DirectSum.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | of i p => rw [sectionScalar_mul_of, of_mul_sectionScalar]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/-- The scalars are carried along the restriction homomorphisms. -/
theorem sectionRestriction_sectionScalar {U V : Cᵒᵖ} (a : V ⟶ U)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj V) :
    (A.sectionRestriction a).toAlgebraHom (A.sectionScalar V r) =
      A.sectionScalar U ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map a r) := by
  rw [sectionScalar_apply, sectionRestriction_of, sectionScalar_apply, sectionRestrictApp_apply,
    PresheafOfModules.map_smul, ← sectionRestrictApp_apply, sectionRestrictApp_one]
  rfl

/-- The scalars of `A(U)`, as a ring homomorphism into the opposite ring. -/
def sectionScalarOp (U : Cᵒᵖ) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U →+* (A.sectionAlgebra U).Aᵐᵒᵖ where
  toFun r := MulOpposite.op (A.sectionScalar U r)
  map_one' := by rw [map_one]; rfl
  map_mul' r s := by
    change MulOpposite.op (A.sectionScalar U (r * s)) =
      MulOpposite.op (A.sectionScalar U s * A.sectionScalar U r)
    rw [← map_mul, show r * s = s * r from @mul_comm (Osharp.obj.obj U) _ r s]
  map_zero' := by rw [map_zero]; rfl
  map_add' r s := by rw [map_add]; rfl

/-- The opposite scalar of `r` is the opposite of the scalar `r · 1`. -/
@[simp] theorem sectionScalarOp_apply (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalarOp U r = MulOpposite.op (A.sectionScalar U r) := rfl

/-- The scalar `r · 1` is closed for the differential of `A(U)`. -/
theorem sectionAlgebra_d_sectionScalar (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    (A.sectionAlgebra U).d (A.sectionScalar U r) = 0 := by
  have h0 : (A.sectionAlgebra U).d
      (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (A.one.eval U)) = 0 := by
    have hone : (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (A.one.eval U) :
        (A.sectionAlgebra U).A) = 1 := DirectSum.of_zero_one _
    have h1 : (1 : (A.sectionAlgebra U).A) ∈ (A.sectionAlgebra U).grading 0 :=
      SetLike.one_mem_graded (A.sectionAlgebra U).grading
    have h' : (A.sectionAlgebra U).d 1 = 0 := by
      simpa using (A.sectionAlgebra U).leibniz 0 0 (1 : (A.sectionAlgebra U).A) 1 h1 h1
    exact (congrArg (A.sectionAlgebra U).d hone).trans h'
  rw [sectionAlgebra_d_of] at h0
  have h1 : (A.complex.d 0 (0 + 1)).val.app U (A.one.eval U) = 0 :=
    DirectSum.of_injective (β := A.toGradedAlgebra.sectionsPiece U) (0 + 1)
      (h0.trans (map_zero _).symm)
  change (A.sectionAlgebra U).d
    (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (r • A.one.eval U)) = 0
  rw [sectionAlgebra_d_of, map_smul, h1, smul_zero, map_zero]
  rfl

/-- The scalars lie in degree zero. -/
theorem sectionScalar_mem (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalar U r ∈ (A.sectionAlgebra U).grading 0 :=
  Stacks.ExternalGrading.of_mem_intSummand _ 0 _

/-! ### Homogeneous sections and scalars, as elements of `A(U)` -/

/-- A homogeneous section of `A` over `U`, as an element of the algebra `A(U)`. -/
def sectionOf (U : Cᵒᵖ) (i : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i) :
    (A.sectionAlgebra U).A :=
  DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i p

/-- A homogeneous section of degree `i` lies in the degree-`i` part of `A(U)`. -/
theorem sectionOf_mem (U : Cᵒᵖ) (i : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i) :
    A.sectionOf U i p ∈ (A.sectionAlgebra U).grading i :=
  Stacks.ExternalGrading.of_mem_intSummand _ i p

/-- `sectionOf` is additive. -/
theorem sectionOf_add (U : Cᵒᵖ) (i : ℤ) (p q : A.toGradedAlgebra.sectionsPiece U i) :
    A.sectionOf U i (p + q) = A.sectionOf U i p + A.sectionOf U i q :=
  map_add (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i) p q

/-- The product in `A(U)` of homogeneous sections of degrees `i` and `j` is their product
`A^i × A^j ⟶ A^{i+j}`. -/
theorem sectionOf_mul (U : Cᵒᵖ) (i j : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i)
    (q : A.toGradedAlgebra.sectionsPiece U j) :
    A.sectionOf U i p * A.sectionOf U j q = A.sectionOf U (i + j) ((A.mul i j).app U p q) :=
  GradedAlgebra.of_mul_of_eq A.toGradedAlgebra U i j p q

/-- The unit section of `A` is the unit of `A(U)`. -/
theorem sectionOf_one (U : Cᵒᵖ) : A.sectionOf U 0 (A.one.eval U) = 1 :=
  DirectSum.of_zero_one _

/-- Heterogeneously equal homogeneous sections of equal degrees are the same element of
`A(U)`. -/
theorem sectionOf_heq (U : Cᵒᵖ) {i j : ℤ} (h : i = j) {p : A.toGradedAlgebra.sectionsPiece U i}
    {q : A.toGradedAlgebra.sectionsPiece U j} (hpq : p ≍ q) :
    A.sectionOf U i p = A.sectionOf U j q :=
  SheafOfModules.of_heq h hpq

/-- The differential of `A(U)` on a homogeneous section is the differential of `A`. -/
theorem sectionAlgebra_d_sectionOf (U : Cᵒᵖ) (i : ℤ) (p : A.toGradedAlgebra.sectionsPiece U i) :
    (A.sectionAlgebra U).d (A.sectionOf U i p) =
      A.sectionOf U (i + 1) ((A.complex.d i (i + 1)).val.app U p) :=
  A.sectionAlgebra_d_of U i p

/-- The restriction homomorphism `A(V) ⟶ A(U)` on a homogeneous section is its restriction in
`A`. -/
theorem sectionRestriction_sectionOf {U V : Cᵒᵖ} (a : V ⟶ U) (i : ℤ)
    (p : A.toGradedAlgebra.sectionsPiece V i) :
    (A.sectionRestriction a).toAlgebraHom (A.sectionOf V i p) =
      A.sectionOf U i ((A.complex.X i).val.map a p) :=
  A.sectionRestriction_of a i p

/-- The scalar `r · 1`, as an element of the algebra `A(U)`. -/
def sectionScalarAlg (U : Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    (A.sectionAlgebra U).A :=
  A.sectionScalar U r

/-- The scalar `r · 1` times a homogeneous section is its scalar multiple. -/
theorem sectionScalarAlg_mul_sectionOf (U : Cᵒᵖ) (i : ℤ)
    (p : A.toGradedAlgebra.sectionsPiece U i)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalarAlg U r * A.sectionOf U i p = A.sectionOf U i (r • p) :=
  A.sectionScalar_mul_of U i p r

/-- A homogeneous section times the scalar `r · 1` is its scalar multiple. -/
theorem sectionOf_mul_sectionScalarAlg (U : Cᵒᵖ) (i : ℤ)
    (p : A.toGradedAlgebra.sectionsPiece U i)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionOf U i p * A.sectionScalarAlg U r = A.sectionOf U i (r • p) :=
  A.of_mul_sectionScalar U i p r

/-- The scalar `r · 1` is central in `A(U)`. -/
theorem sectionScalarAlg_mul_comm (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) (x : (A.sectionAlgebra U).A) :
    A.sectionScalarAlg U r * x = x * A.sectionScalarAlg U r :=
  A.sectionScalar_mul_comm U r x

/-- The opposite scalar of `r` is the opposite of the element `r · 1` of `A(U)`. -/
theorem sectionScalarOp_eq (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) :
    A.sectionScalarOp U r = MulOpposite.op (A.sectionScalarAlg U r) :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable (A : DifferentialGradedAlgebra.{t, m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- **A presheaf of section modules** over a sheaf of differential graded algebras `A` on a
chaotic site: a right differential graded `A(U)`-module `X(U)` for every object `U`, and for
every morphism `a : V ⟶ U` of `Cᵒᵖ` a homomorphism `X(V) ⟶ X(U)` of differential graded
`A(V)`-modules, `X(U)` being read over `A(V)` through the restriction homomorphism
`A(V) ⟶ A(U)`, the homomorphisms composing on the nose. -/
structure SectionSystem where
  /-- The differential graded `A(U)`-module over `U`. -/
  obj (U : Cᵒᵖ) : _root_.DifferentialGradedModule.{m, m, m} (A.sectionAlgebra U)
  /-- The restriction homomorphism along a morphism of `Cᵒᵖ`. -/
  restr {U V : Cᵒᵖ} (a : V ⟶ U) :
    (obj V).Hom
      (_root_.DifferentialGradedModule.restrictScalars (A.sectionRestriction a) (obj U))
  /-- Restriction along an identity is the identity. -/
  restr_id (U : Cᵒᵖ) (x : (obj U).M) : (restr (𝟙 U)).toFun x = x
  /-- Restriction along a composite is the composite of the restrictions. -/
  restr_comp {U V W : Cᵒᵖ} (a : V ⟶ U) (b : W ⟶ V) (x : (obj W).M) :
    (restr (b ≫ a)).toFun x = (restr a).toFun ((restr b).toFun x)

namespace SectionSystem

variable {A} (X : SectionSystem A)

/-- The scalar `r · 1` keeps a homogeneous element in its degree. -/
theorem scalar_smul_mem (U : Cᵒᵖ) (n : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) {x : (X.obj U).M}
    (hx : x ∈ (X.obj U).grading n) :
    A.sectionScalarOp U r • x ∈ (X.obj U).grading n :=
  _root_.DifferentialGradedModule.mem_grading_congr (add_zero n)
    ((X.obj U).smul_mem n 0 x _ hx (A.sectionScalar_mem U r))

/-- The degree-`n` part of `X(U)` is a module over the sections of the sheaf of rings, which act
through the scalars `r · 1` of `A(U)`. -/
@[instance_reducible]
def pieceModule (U : Cᵒᵖ) (n : ℤ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) ((X.obj U).grading n) where
  smul r x := ⟨A.sectionScalarOp U r • (x : (X.obj U).M), X.scalar_smul_mem U n r x.2⟩
  one_smul x := Subtype.ext (by
    change A.sectionScalarOp U 1 • (x : (X.obj U).M) = x
    rw [map_one, one_smul])
  mul_smul r s x := Subtype.ext (by
    change A.sectionScalarOp U (r * s) • (x : (X.obj U).M) =
      A.sectionScalarOp U r • A.sectionScalarOp U s • (x : (X.obj U).M)
    rw [map_mul, mul_smul])
  smul_zero r := Subtype.ext (smul_zero (A.sectionScalarOp U r))
  smul_add r x y := Subtype.ext (smul_add (A.sectionScalarOp U r) (x : (X.obj U).M) y)
  add_smul r s x := Subtype.ext (by
    change A.sectionScalarOp U (r + s) • (x : (X.obj U).M) =
      A.sectionScalarOp U r • (x : (X.obj U).M) + A.sectionScalarOp U s • (x : (X.obj U).M)
    rw [map_add, add_smul])
  zero_smul x := Subtype.ext (by
    change A.sectionScalarOp U 0 • (x : (X.obj U).M) = 0
    rw [map_zero, zero_smul])

attribute [local instance] pieceModule

/-- A section `r` acts on the degree-`n` part of `X(U)` as the scalar `r · 1`. -/
@[simp] theorem coe_piece_smul (U : Cᵒᵖ) (n : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) (x : (X.obj U).grading n) :
    ((r • x : (X.obj U).grading n) : (X.obj U).M) = A.sectionScalarOp U r • (x : (X.obj U).M) :=
  rfl

/-- The restriction homomorphism, as a map into `X(U)` itself. -/
def restrFun {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) : (X.obj U).M :=
  (X.restr a).toFun x

/-- `restrFun a` is the underlying map of the restriction homomorphism along `a`. -/
theorem restrFun_apply {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    X.restrFun a x = (X.restr a).toFun x := rfl

/-- Restriction is semilinear along the restriction homomorphism of the section algebras. -/
theorem restrFun_smul {U V : Cᵒᵖ} (a : V ⟶ U) (b : (A.sectionAlgebra V).A) (x : (X.obj V).M) :
    X.restrFun a (MulOpposite.op b • x) =
      MulOpposite.op ((A.sectionRestriction a).toAlgebraHom b) • X.restrFun a x :=
  (X.restr a).map_smul x b

/-- Restriction commutes with the differentials. -/
theorem restrFun_d {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    X.restrFun a ((X.obj V).d x) = (X.obj U).d (X.restrFun a x) :=
  congrArg (fun f => f x) (X.restr a).map_d

/-- Restriction is additive. -/
theorem restrFun_add {U V : Cᵒᵖ} (a : V ⟶ U) (x y : (X.obj V).M) :
    X.restrFun a (x + y) = X.restrFun a x + X.restrFun a y :=
  map_add (X.restr a).toFun x y

/-- Restriction of a homogeneous element along a morphism of `Cᵒᵖ`. -/
def restrictPiece {U V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ) :
    (X.obj V).grading n →+ (X.obj U).grading n where
  toFun x := ⟨(X.restr a).toFun x, (X.restr a).map_grading n x x.2⟩
  map_zero' := Subtype.ext (map_zero (X.restr a).toFun)
  map_add' x y := Subtype.ext (map_add (X.restr a).toFun (x : (X.obj V).M) y)

/-- The restriction of a homogeneous element is its image under the restriction homomorphism. -/
@[simp] theorem coe_restrictPiece {U V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ) (x : (X.obj V).grading n) :
    ((X.restrictPiece a n x : (X.obj U).grading n) : (X.obj U).M) = (X.restr a).toFun x :=
  rfl

/-- The degree-`n` piece of the realization, as a presheaf of abelian groups. -/
def piecePresheaf (n : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{m} where
  obj U := AddCommGrpCat.of ((X.obj U).grading n)
  map a := AddCommGrpCat.ofHom (X.restrictPiece a n)
  map_id U := by
    ext x
    exact X.restr_id U _
  map_comp b a := by
    ext x
    exact X.restr_comp a b _

/-- Restriction is semilinear along the restriction maps of the sheaf of rings. -/
theorem restrictPiece_smul {U V : Cᵒᵖ} (a : V ⟶ U) (n : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj V) (x : (X.obj V).grading n) :
    X.restrictPiece a n (r • x) =
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map a r • X.restrictPiece a n x := by
  refine Subtype.ext ?_
  change X.restrFun a (A.sectionScalarOp V r • (x : (X.obj V).M)) =
    A.sectionScalarOp U _ • X.restrFun a x
  refine (X.restrFun_smul a (A.sectionScalar V r) x).trans ?_
  rw [A.sectionRestriction_sectionScalar]
  rfl

/-- **The degree-`n` piece of the realization**, a sheaf of modules. -/
def pieceSheaf (n : ℤ) : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) where
  val :=
    letI : ∀ U : Cᵒᵖ, Module ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
        ((X.piecePresheaf n).obj U) := fun U => X.pieceModule U n
    PresheafOfModules.ofPresheaf (X.piecePresheaf n)
      (fun _ _ a r x => X.restrictPiece_smul a n r x)
  isSheaf := Presheaf.isSheaf_bot _

/-- The sections over `U` of the degree-`n` piece of the realization are the degree-`n` part of
`X(U)`. -/
theorem pieceSheaf_obj (n : ℤ) (U : Cᵒᵖ) :
    ((X.pieceSheaf n).val.obj U : Type m) = (X.obj U).grading n := rfl

/-- A section of the degree-`n` piece of the realization is a homogeneous element of `X(U)`. -/
def pieceElt {n : ℤ} {U : Cᵒᵖ} (x : (X.pieceSheaf n).val.obj U) : (X.obj U).grading n := x

/-- A homogeneous element of `X(U)` is a section of the degree-`n` piece of the realization. -/
def eltPiece {n : ℤ} {U : Cᵒᵖ} (x : (X.obj U).grading n) : (X.pieceSheaf n).val.obj U := x

/-- `pieceElt` is a left inverse of `eltPiece`. -/
@[simp] theorem pieceElt_eltPiece {n : ℤ} {U : Cᵒᵖ} (x : (X.obj U).grading n) :
    X.pieceElt (X.eltPiece x) = x := rfl

/-- `eltPiece` is a left inverse of `pieceElt`. -/
@[simp] theorem eltPiece_pieceElt {n : ℤ} {U : Cᵒᵖ} (x : (X.pieceSheaf n).val.obj U) :
    X.eltPiece (X.pieceElt x) = x := rfl

/-- Two sections of the degree-`n` piece are equal if they are equal as elements of `X(U)`. -/
theorem pieceElt_injective {n : ℤ} {U : Cᵒᵖ} {x y : (X.pieceSheaf n).val.obj U}
    (h : ((X.pieceElt x : (X.obj U).grading n) : (X.obj U).M) = X.pieceElt y) : x = y :=
  Subtype.ext h

/-- The restriction maps of the degree-`n` piece are the restrictions of homogeneous
elements. -/
@[simp] theorem pieceSheaf_map_apply (n : ℤ) {U V : Cᵒᵖ} (a : V ⟶ U)
    (x : (X.obj V).grading n) :
    (X.pieceSheaf n).val.map a x = X.restrictPiece a n x := rfl

/-! ### The differential and the action -/

/-- The differential of `X(U)` commutes with the scalars `r · 1`. -/
theorem d_scalar_smul (U : Cᵒᵖ) (n : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) {x : (X.obj U).M}
    (hx : x ∈ (X.obj U).grading n) :
    (X.obj U).d (A.sectionScalarOp U r • x) = A.sectionScalarOp U r • (X.obj U).d x := by
  have h := (X.obj U).leibniz n 0 x (A.sectionScalarAlg U r) hx (A.sectionScalar_mem U r)
  have h0 : (A.sectionAlgebra U).d (A.sectionScalarAlg U r) = 0 :=
    A.sectionAlgebra_d_sectionScalar U r
  rwa [h0, MulOpposite.op_zero, zero_smul, smul_zero, add_zero] at h

/-- The differential of `X(U)` on the degree-`n` part. -/
def dPiece (U : Cᵒᵖ) (n : ℤ) : (X.obj U).grading n →+ (X.obj U).grading (n + 1) where
  toFun x := ⟨(X.obj U).d x, (X.obj U).d_mem n x x.2⟩
  map_zero' := Subtype.ext (map_zero (X.obj U).d)
  map_add' x y := Subtype.ext (map_add (X.obj U).d (x : (X.obj U).M) y)

/-- `dPiece` is the differential of `X(U)`. -/
@[simp] theorem coe_dPiece (U : Cᵒᵖ) (n : ℤ) (x : (X.obj U).grading n) :
    ((X.dPiece U n x : (X.obj U).grading (n + 1)) : (X.obj U).M) = (X.obj U).d x :=
  rfl

/-- The differential of the realization, as a morphism of presheaves of abelian groups. -/
def dPresheaf (n : ℤ) : X.piecePresheaf n ⟶ X.piecePresheaf (n + 1) where
  app U := AddCommGrpCat.ofHom (X.dPiece U n)
  naturality V U a := by
    ext x
    exact Subtype.ext (X.restrFun_d a ((show (X.obj V).grading n from x) : (X.obj V).M)).symm

/-- **The differential of the realization.** -/
def dSheaf (n : ℤ) : X.pieceSheaf n ⟶ X.pieceSheaf (n + 1) :=
  ⟨PresheafOfModules.homMk (X.dPresheaf n)
    (fun U r x => Subtype.ext (X.d_scalar_smul U n r (X.pieceElt x).2))⟩

/-- On sections over `U`, the differential of the realization is the differential of `X(U)`. -/
@[simp] theorem dSheaf_val_app_apply (n : ℤ) (U : Cᵒᵖ) (x : (X.pieceSheaf n).val.obj U) :
    X.pieceElt ((X.dSheaf n).val.app U x) = X.dPiece U n (X.pieceElt x) :=
  rfl

/-- The differential of the realization squares to zero. -/
theorem dSheaf_comp_dSheaf (n : ℤ) : X.dSheaf n ≫ X.dSheaf (n + 1) = 0 := by
  apply SheafOfModules.hom_ext
  ext U x
  exact Subtype.ext (congrArg (fun f => f ((X.pieceElt x : (X.obj U).grading n) : (X.obj U).M))
    (X.obj U).d_comp_d)

/-- The cochain complex of sheaves of modules underlying the realization. -/
def complex :
    CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) ℤ :=
  CochainComplex.of X.pieceSheaf X.dSheaf X.dSheaf_comp_dSheaf

/-- The degree-`n` term of the complex is the degree-`n` piece of the realization. -/
theorem complex_X (n : ℤ) : X.complex.X n = X.pieceSheaf n := rfl

/-- The differential of the complex is the differential of the realization. -/
theorem complex_d (n : ℤ) : X.complex.d n (n + 1) = X.dSheaf n :=
  CochainComplex.of_d _ _ n

/-- A section of the degree-`n` term of the complex of the realization is a homogeneous element
of `X(U)`. -/
def cElt {n : ℤ} {U : Cᵒᵖ} (x : (X.complex.X n).val.obj U) : (X.obj U).grading n := x

/-- Two sections of the degree-`n` term of the complex are equal if they are equal as elements
of `X(U)`. -/
theorem cElt_injective {n : ℤ} {U : Cᵒᵖ} {x y : (X.complex.X n).val.obj U}
    (h : ((X.cElt x : (X.obj U).grading n) : (X.obj U).M) = X.cElt y) : x = y :=
  Subtype.ext h

/-- Sections of the terms of degrees `i = j` of the complex that are equal as elements of
`X(U)` are heterogeneously equal. -/
theorem cElt_heq {U : Cᵒᵖ} {i j : ℤ} (h : i = j) {x : (X.complex.X i).val.obj U}
    {y : (X.complex.X j).val.obj U}
    (hxy : ((X.cElt x : (X.obj U).grading i) : (X.obj U).M) =
      (X.cElt y : (X.obj U).grading j)) : x ≍ y := by
  subst h
  exact heq_of_eq (Subtype.ext hxy)

/-- `cElt` is additive, as a map into `X(U)`. -/
theorem coe_cElt_add {n : ℤ} {U : Cᵒᵖ} (x y : (X.complex.X n).val.obj U) :
    ((X.cElt (x + y) : (X.obj U).grading n) : (X.obj U).M) =
      (X.cElt x : (X.obj U).grading n) + ((X.cElt y : (X.obj U).grading n) : (X.obj U).M) :=
  rfl

/-- `cElt` preserves subtraction, as a map into `X(U)`. -/
theorem coe_cElt_sub {n : ℤ} {U : Cᵒᵖ} (x y : (X.complex.X n).val.obj U) :
    ((X.cElt (x - y) : (X.obj U).grading n) : (X.obj U).M) =
      (X.cElt x : (X.obj U).grading n) - ((X.cElt y : (X.obj U).grading n) : (X.obj U).M) :=
  rfl

/-- `cElt` preserves integer multiples, as a map into `X(U)`. -/
theorem coe_cElt_zsmul {n : ℤ} {U : Cᵒᵖ} (k : ℤ) (x : (X.complex.X n).val.obj U) :
    ((X.cElt (k • x) : (X.obj U).grading n) : (X.obj U).M) =
      k • ((X.cElt x : (X.obj U).grading n) : (X.obj U).M) :=
  rfl

/-- Transporting a section along an equality of degrees does not change it as an element of
`X(U)`. -/
theorem coe_cElt_gradedCast (U : Cᵒᵖ) {i j : ℤ} (h : i = j) (x : (X.complex.X i).val.obj U) :
    ((X.cElt (gradedCast (fun q => ((X.complex.X q).val.obj U : Type m)) h x) :
      (X.obj U).grading j) : (X.obj U).M) = (X.cElt x : (X.obj U).grading i) := by
  subst h
  rfl

/-- The differential of the complex is the differential of `X(U)`. -/
theorem coe_cElt_d {k : ℤ} {U : Cᵒᵖ} (z : (X.complex.X k).val.obj U) :
    ((X.cElt ((X.complex.d k (k + 1)).val.app U z) : (X.obj U).grading (k + 1)) :
      (X.obj U).M) = (X.obj U).d (X.cElt z : (X.obj U).grading k) := by
  rw [complex_d]
  rfl

/-- The right action of a homogeneous section of `A` on the degree-`n` part of `X(U)`. -/
def mulPiece (U : Cᵒᵖ) (n i : ℤ) :
    (X.obj U).grading n →+ (A.complex.X i).val.obj U →+ (X.obj U).grading (n + i) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun p => ⟨MulOpposite.op (A.sectionOf U i p) • (x : (X.obj U).M),
        (X.obj U).smul_mem n i x _ x.2 (A.sectionOf_mem U i p)⟩)
      (fun p q => Subtype.ext (by
        change MulOpposite.op (A.sectionOf U i (p + q)) • (x : (X.obj U).M) =
          MulOpposite.op (A.sectionOf U i p) • (x : (X.obj U).M) +
            MulOpposite.op (A.sectionOf U i q) • (x : (X.obj U).M)
        rw [A.sectionOf_add, MulOpposite.op_add, add_smul])))
    (fun x y => AddMonoidHom.ext fun p => Subtype.ext
      (smul_add (MulOpposite.op (A.sectionOf U i p)) (x : (X.obj U).M) y))

/-- `mulPiece` is the right action of the section `p`, as an element of `A(U)`. -/
@[simp] theorem coe_mulPiece (U : Cᵒᵖ) (n i : ℤ) (x : (X.obj U).grading n)
    (p : (A.complex.X i).val.obj U) :
    ((X.mulPiece U n i x p : (X.obj U).grading (n + i)) : (X.obj U).M) =
      MulOpposite.op (A.sectionOf U i p) • (x : (X.obj U).M) :=
  rfl

/-- The scalars commute with the right action. -/
theorem scalar_smul_comm (U : Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U) (b : (A.sectionAlgebra U).A)
    (x : (X.obj U).M) :
    MulOpposite.op b • A.sectionScalarOp U r • x =
      A.sectionScalarOp U r • MulOpposite.op b • x := by
  rw [A.sectionScalarOp_eq, ← mul_smul, ← mul_smul, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
    A.sectionScalarAlg_mul_comm]

/-- **The right action of the realization**, a bilinear map of sheaves of modules. -/
def mul (n i : ℤ) : BilinearMap (X.complex.X n) (A.complex.X i) (X.complex.X (n + i)) where
  app U := X.mulPiece U n i
  map_smul_left U r x p := Subtype.ext
    (X.scalar_smul_comm U r (A.sectionOf U i p) (X.cElt x : (X.obj U).grading n))
  map_smul_right U r x p := Subtype.ext (by
    change MulOpposite.op (A.sectionOf U i (r • p)) • ((X.cElt x : (X.obj U).grading n) :
        (X.obj U).M) =
      A.sectionScalarOp U r • MulOpposite.op (A.sectionOf U i p) •
        ((X.cElt x : (X.obj U).grading n) : (X.obj U).M)
    rw [← X.scalar_smul_comm, A.sectionScalarOp_eq, ← mul_smul, ← MulOpposite.op_mul,
      A.sectionScalarAlg_mul_sectionOf])
  naturality {V U} a x p := Subtype.ext (by
    change X.restrFun a (MulOpposite.op (A.sectionOf V i p) •
        ((X.cElt x : (X.obj V).grading n) : (X.obj V).M)) =
      MulOpposite.op (A.sectionOf U i ((A.complex.X i).val.map a p)) •
        X.restrFun a ((X.cElt x : (X.obj V).grading n) : (X.obj V).M)
    rw [X.restrFun_smul, A.sectionRestriction_sectionOf])

/-- The right action of the realization is the right action on `X(U)`. -/
theorem coe_cElt_mul {n i : ℤ} {U : Cᵒᵖ} (x : (X.complex.X n).val.obj U)
    (p : (A.complex.X i).val.obj U) :
    ((X.cElt ((X.mul n i).app U x p) : (X.obj U).grading (n + i)) : (X.obj U).M) =
      MulOpposite.op (A.sectionOf U i p) • ((X.cElt x : (X.obj U).grading n) : (X.obj U).M) :=
  rfl

/-- **The realization of a presheaf of section modules**: the right differential graded
`A`-module whose degree-`n` piece is `U ↦ X(U)ⁿ`, with the right action and the differential of
the modules `X(U)`. -/
abbrev realize : DifferentialGradedModule.{t, m, m} A where
  complex := X.complex
  mul := X.mul
  mul_assoc n i j U x p q := X.cElt_heq (add_assoc n i j) (by
    rw [X.coe_cElt_mul, X.coe_cElt_mul, X.coe_cElt_mul, ← mul_smul, ← MulOpposite.op_mul,
      A.sectionOf_mul])
  mul_one n U x := X.cElt_heq (add_zero n) (by
    rw [X.coe_cElt_mul, A.sectionOf_one, MulOpposite.op_one, one_smul])
  leibniz n i U x p := by
    apply X.cElt_injective
    rw [X.coe_cElt_d, X.coe_cElt_mul, X.coe_cElt_add, X.coe_cElt_zsmul, X.coe_cElt_gradedCast,
      X.coe_cElt_gradedCast, X.coe_cElt_mul, X.coe_cElt_mul, X.coe_cElt_d,
      (X.obj U).leibniz n i _ _ (X.cElt x).2 (A.sectionOf_mem U i p),
      A.sectionAlgebra_d_sectionOf]

/-- The underlying complex of the realization is `complex`. -/
@[simp] theorem realize_complex : X.realize.complex = X.complex := rfl

/-- The right action of the realization is `mul`. -/
@[simp] theorem realize_mul (n i : ℤ) : X.realize.mul n i = X.mul n i := rfl

/-- The differential of the realization is `dSheaf`. -/
theorem realize_complex_d (n : ℤ) : X.realize.complex.d n (n + 1) = X.dSheaf n :=
  X.complex_d n

/-! ### The sections of the realization -/

/-- An additive map between modules over the lifted integers is linear, for any two module
structures. -/
def uliftLinear {M N : Type*} [AddCommGroup M] [AddCommGroup N] (iM : Module (ULift.{m} ℤ) M)
    (iN : Module (ULift.{m} ℤ) N) (f : M →+ N) :
    @LinearMap (ULift.{m} ℤ) (ULift.{m} ℤ) _ _ (RingHom.id _) M N _ _ iM iN where
  toFun := f
  map_add' := map_add f
  map_smul' c x := by
    have h1 := @Int.cast_smul_eq_zsmul (ULift.{m} ℤ) M _ _ iM c.down x
    have h2 := @Int.cast_smul_eq_zsmul (ULift.{m} ℤ) N _ _ iN c.down (f x)
    exact (congrArg f h1).trans ((map_zsmul f c.down x).trans h2.symm)

/-- The sections of the realization over `U` are `X(U)`: the direct sum of the homogeneous parts
of `X(U)` is `X(U)` itself. -/
def sectionsAddEquiv (U : Cᵒᵖ) : X.realize.totalSections U ≃+ (X.obj U).M :=
  (DirectSum.decomposeAddEquiv (X.obj U).grading).symm

/-- The identification of the sections sends a homogeneous section to itself in `X(U)`. -/
theorem sectionsAddEquiv_of (U : Cᵒᵖ) (n : ℤ) (x : X.realize.sectionsPiece U n) :
    X.sectionsAddEquiv U (DirectSum.of (X.realize.sectionsPiece U) n x) =
      (X.cElt x : (X.obj U).grading n) :=
  DirectSum.decompose_symm_of (ℳ := (X.obj U).grading) (i := n) (X.cElt x)

/-- The right action of the sections of `A` on a fixed element of `X(U)`, as an additive map in
the section. -/
def opSMulHom (U : Cᵒᵖ) (y : (X.obj U).M) : A.toGradedAlgebra.totalSections U →+ (X.obj U).M :=
  AddMonoidHom.mk' (fun s => MulOpposite.op (show (A.sectionAlgebra U).A from s) • y)
    (fun s s' => by
      rw [show (show (A.sectionAlgebra U).A from s + s') =
        (show (A.sectionAlgebra U).A from s) + (show (A.sectionAlgebra U).A from s') from rfl,
        MulOpposite.op_add, add_smul])

/-- The identification of the sections carries the action of `A(U)` on the sections of the
realization to its action on `X(U)`. -/
theorem sectionsAddEquiv_act (U : Cᵒᵖ) (x : X.realize.totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    X.sectionsAddEquiv U (X.realize.act U x s) = X.opSMulHom U (X.sectionsAddEquiv U x) s := by
  induction x using DirectSum.induction_on generalizing s with
  | zero =>
      rw [map_zero, AddMonoidHom.zero_apply, map_zero]
      exact (smul_zero _).symm
  | add x y hx hy =>
      rw [map_add, AddMonoidHom.add_apply, map_add, hx, hy, map_add]
      exact (smul_add _ _ _).symm
  | of n p =>
      have key : (X.sectionsAddEquiv U).toAddMonoidHom.comp
          (X.realize.act U (DirectSum.of (X.realize.sectionsPiece U) n p)) =
          X.opSMulHom U (X.sectionsAddEquiv U (DirectSum.of (X.realize.sectionsPiece U) n p)) := by
        refine DirectSum.addHom_ext fun i q => ?_
        rw [AddMonoidHom.comp_apply, act_of, actOn_of, AddEquiv.coe_toAddMonoidHom,
          sectionsAddEquiv_of, sectionsAddEquiv_of]
        rfl
      exact DFunLike.congr_fun key s

/-- **The comparison of the sections of the realization with `X(U)`**, a homomorphism of
differential graded `A(U)`-modules. -/
def sectionsHom (U : Cᵒᵖ) : (X.realize.sectionModule U).Hom (X.obj U) where
  toFun := uliftLinear (X.realize.sectionModule U).module (X.obj U).module
    (X.sectionsAddEquiv U).toAddMonoidHom
  map_smul x s := X.sectionsAddEquiv_act U x s
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change X.sectionsAddEquiv U (DirectSum.of (X.realize.sectionsPiece U) n p) ∈ _
    rw [sectionsAddEquiv_of]
    exact (X.cElt p).2
  map_d := DFunLike.ext _ _ fun x => by
    change X.sectionsAddEquiv U (X.realize.sectionD U x) = (X.obj U).d (X.sectionsAddEquiv U x)
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | of n p =>
        rw [sectionD_of, sectionsAddEquiv_of, sectionsAddEquiv_of]
        exact X.coe_cElt_d p

/-- The underlying map of `sectionsHom` is `sectionsAddEquiv`. -/
@[simp] theorem sectionsHom_toFun (U : Cᵒᵖ) (x : X.realize.totalSections U) :
    (X.sectionsHom U).toFun x = X.sectionsAddEquiv U x := rfl

/-- **The sections of the realization over `U` are `X(U)`**, as differential graded
`A(U)`-modules. -/
def sectionsIso (U : Cᵒᵖ) : X.realize.sectionModule U ≅ X.obj U :=
  _root_.DifferentialGradedModule.Hom.isoOfBijective (X.sectionsHom U)
    (X.sectionsAddEquiv U).bijective

/-- The underlying map of `sectionsIso` is `sectionsAddEquiv`. -/
@[simp] theorem sectionsIso_hom_toFun (U : Cᵒᵖ) (x : X.realize.totalSections U) :
    (X.sectionsIso U).hom.toFun x = X.sectionsAddEquiv U x := rfl

/-- An additive comparison of the sections of two realizations with the modules `X(U)` can be
checked on homogeneous sections. -/
private theorem sectionsAddEquiv_map_eq {Y : SectionSystem A} {U V : Cᵒᵖ}
    (φ : X.realize.totalSections V →+ Y.realize.totalSections U) (ψ : (X.obj V).M →+ (Y.obj U).M)
    (h : ∀ (n : ℤ) (p : X.realize.sectionsPiece V n),
      Y.sectionsAddEquiv U (φ (DirectSum.of (X.realize.sectionsPiece V) n p)) =
        ψ (X.sectionsAddEquiv V (DirectSum.of (X.realize.sectionsPiece V) n p)))
    (x : X.realize.totalSections V) :
    Y.sectionsAddEquiv U (φ x) = ψ (X.sectionsAddEquiv V x) :=
  DFunLike.congr_fun
    (DirectSum.addHom_ext (f := (Y.sectionsAddEquiv U).toAddMonoidHom.comp φ)
      (g := ψ.comp (X.sectionsAddEquiv V).toAddMonoidHom) h) x

/-- The identification of the sections is compatible with restriction: restricting the sections
of the realization is restricting in `X`. -/
theorem sectionsAddEquiv_sectionRestrictAdd {U V : Cᵒᵖ} (a : V ⟶ U)
    (x : X.realize.totalSections V) :
    X.sectionsAddEquiv U (X.realize.sectionRestrictAdd a x) =
      X.restrFun a (X.sectionsAddEquiv V x) :=
  X.sectionsAddEquiv_map_eq (X.realize.sectionRestrictAdd a) (X.restr a).toFun.toAddMonoidHom
    (fun n p => by
      rw [sectionRestrictAdd_of, sectionsAddEquiv_of, sectionsAddEquiv_of]
      rfl) x

/-- **The identification of the sections intertwines the restriction maps**, as an equality of
homomorphisms of differential graded `A(V)`-modules. -/
theorem sectionModuleRestriction_sectionsIso {U V : Cᵒᵖ} (a : V ⟶ U) :
    X.realize.sectionModuleRestriction a ≫
        _root_.DifferentialGradedModule.restrictScalarsHom (A.sectionRestriction a)
          (X.sectionsIso U).hom =
      (X.sectionsIso V).hom ≫ X.restr a :=
  _root_.DifferentialGradedModule.Hom.ext
    (DFunLike.ext _ _ fun x => X.sectionsAddEquiv_sectionRestrictAdd a x)

/-! ### Morphisms -/

/-- A morphism of presheaves of section modules: homomorphisms `X(U) ⟶ Y(U)` of differential
graded `A(U)`-modules commuting with the restriction homomorphisms. -/
@[ext]
structure Hom (X Y : SectionSystem A) where
  /-- The homomorphism over `U`. -/
  app (U : Cᵒᵖ) : X.obj U ⟶ Y.obj U
  /-- The homomorphisms commute with restriction. -/
  naturality {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    Y.restrFun a ((app V).toFun x) = (app U).toFun (X.restrFun a x)

/-- The category of presheaves of section modules. -/
instance : Category (SectionSystem A) where
  Hom := Hom
  id X := ⟨fun U => 𝟙 (X.obj U), fun _ _ => rfl⟩
  comp f g := ⟨fun U => f.app U ≫ g.app U, fun a x => by
    change _ = (g.app _).toFun ((f.app _).toFun _)
    rw [← f.naturality, ← g.naturality]
    rfl⟩

/-- Morphisms of presheaves of section modules agreeing over every object are equal. -/
@[ext]
theorem hom_ext {X Y : SectionSystem A} {f g : X ⟶ Y} (h : ∀ U, f.app U = g.app U) : f = g :=
  Hom.ext (funext h)

/-- The identity morphism is the identity over every object. -/
@[simp] theorem id_app (U : Cᵒᵖ) : (𝟙 X : X ⟶ X).app U = 𝟙 (X.obj U) := rfl

/-- A composite morphism is the composite over every object. -/
@[simp] theorem comp_app {Y Z : SectionSystem A} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Cᵒᵖ) :
    (f ≫ g).app U = f.app U ≫ g.app U := rfl

variable {X} {Y Z : SectionSystem A}

/-- A morphism of presheaves of section modules on the degree-`n` part over `U`. -/
def appPiece (f : X ⟶ Y) (U : Cᵒᵖ) (n : ℤ) : (X.obj U).grading n →+ (Y.obj U).grading n where
  toFun x := ⟨(f.app U).toFun x, (f.app U).map_grading n x x.2⟩
  map_zero' := Subtype.ext (map_zero (f.app U).toFun)
  map_add' x y := Subtype.ext (map_add (f.app U).toFun (x : (X.obj U).M) y)

/-- A morphism of presheaves of section modules, on the degree-`n` pieces of the realizations. -/
def pieceMap (f : X ⟶ Y) (n : ℤ) : X.pieceSheaf n ⟶ Y.pieceSheaf n :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (appPiece f U n)
      naturality := fun V U a => by
        ext x
        exact Subtype.ext
          (f.naturality a ((show (X.obj V).grading n from x) : (X.obj V).M)).symm }
    (fun U r x => Subtype.ext ((f.app U).map_smul _ _))⟩

/-- On sections over `U`, `pieceMap f` is the homomorphism `f.app U`. -/
theorem coe_pieceMap (f : X ⟶ Y) (n : ℤ) (U : Cᵒᵖ) (x : (X.complex.X n).val.obj U) :
    ((Y.cElt ((pieceMap f n).val.app U x) : (Y.obj U).grading n) : (Y.obj U).M) =
      (f.app U).toFun (X.cElt x : (X.obj U).grading n) :=
  rfl

/-- **The realization of a morphism of presheaves of section modules.** -/
def realizeMap (f : X ⟶ Y) : X.realize ⟶ Y.realize where
  toHomologicalComplex := CochainComplex.ofHom (pieceMap f) (fun n => by
    rw [X.realize_complex_d, Y.realize_complex_d]
    apply SheafOfModules.hom_ext
    ext U x
    refine Subtype.ext ?_
    exact (congrArg (fun g => g ((X.cElt x : (X.obj U).grading n) : (X.obj U).M))
      (f.app U).map_d).symm)
  map_mul n i U x p := Subtype.ext ((f.app U).map_smul _ _)

/-- On sections over `U`, the realization of `f` is the homomorphism `f.app U`. -/
theorem coe_realizeMap_f (f : X ⟶ Y) (n : ℤ) (U : Cᵒᵖ) (x : (X.complex.X n).val.obj U) :
    ((Y.cElt (((realizeMap f).toHomologicalComplex.f n).val.app U x) : (Y.obj U).grading n) :
      (Y.obj U).M) = (f.app U).toFun (X.cElt x : (X.obj U).grading n) :=
  rfl

variable (A) in
/-- **The realization functor** from presheaves of section modules to right differential graded
`A`-modules. -/
def realizeFunctor : SectionSystem A ⥤ DifferentialGradedModule.{t, m, m} A where
  obj X := X.realize
  map f := realizeMap f
  map_id X := by
    apply DifferentialGradedModule.Hom.ext
    intro n
    apply SheafOfModules.hom_ext
    ext U x
    rfl
  map_comp f g := by
    apply DifferentialGradedModule.Hom.ext
    intro n
    apply SheafOfModules.hom_ext
    ext U x
    rfl

/-- The realization functor sends `X` to its realization. -/
@[simp] theorem realizeFunctor_obj (X : SectionSystem A) :
    (realizeFunctor A).obj X = X.realize := rfl

/-- The realization functor sends `f` to its realization. -/
@[simp] theorem realizeFunctor_map (f : X ⟶ Y) : (realizeFunctor A).map f = realizeMap f := rfl

/-- The identification of the sections of the realization is natural in the presheaf of section
modules. -/
theorem sectionsIso_naturality (f : X ⟶ Y) (U : Cᵒᵖ) :
    sectionMap (realizeMap f) U ≫ (Y.sectionsIso U).hom = (X.sectionsIso U).hom ≫ f.app U := by
  refine _root_.DifferentialGradedModule.Hom.ext (DFunLike.ext _ _ fun x => ?_)
  exact X.sectionsAddEquiv_map_eq (sectionMapAdd (realizeMap f) U) (f.app U).toFun.toAddMonoidHom
    (fun n p => by
      rw [sectionMapAdd_of, sectionsAddEquiv_of, sectionsAddEquiv_of]
      rfl) x

/-! ### Homotopies -/

/-- The differential of the complex from degree `i` to degree `j = i + 1` is the differential of
`X(U)`. -/
theorem coe_cElt_d' {i j : ℤ} (hij : i + 1 = j) {U : Cᵒᵖ} (z : (X.complex.X i).val.obj U) :
    ((X.cElt ((X.complex.d i j).val.app U z) : (X.obj U).grading j) : (X.obj U).M) =
      (X.obj U).d (X.cElt z : (X.obj U).grading i) := by
  subst hij
  exact X.coe_cElt_d z

/-- The identification of terms of the complex along an equality of degrees does not change a
section as an element of `X(U)`. -/
theorem coe_cElt_eqToHom {i j : ℤ} (hij : i = j) {U : Cᵒᵖ} (z : (X.complex.X i).val.obj U) :
    ((X.cElt ((eqToHom (congrArg X.complex.X hij)).val.app U z) : (X.obj U).grading j) :
      (X.obj U).M) = (X.cElt z : (X.obj U).grading i) := by
  subst hij
  rfl

/-- A homotopy between two morphisms of presheaves of section modules: homotopies over every
object, commuting with the restriction homomorphisms. -/
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy over `U`. -/
  app (U : Cᵒᵖ) : _root_.DifferentialGradedModule.Homotopy (f.app U) (g.app U)
  /-- The homotopies commute with restriction. -/
  naturality {U V : Cᵒᵖ} (a : V ⟶ U) (x : (X.obj V).M) :
    Y.restrFun a ((app V).toLinearMap x) = (app U).toLinearMap (X.restrFun a x)

namespace Homotopy

variable {f g : X ⟶ Y} (h : Homotopy f g)

/-- A homotopy on the degree-`n` part over `U`. -/
def appPiece (U : Cᵒᵖ) (n : ℤ) : (X.obj U).grading n →+ (Y.obj U).grading (n - 1) where
  toFun x := ⟨(h.app U).toLinearMap x, (h.app U).map_grading n x x.2⟩
  map_zero' := Subtype.ext (map_zero (h.app U).toLinearMap)
  map_add' x y := Subtype.ext (map_add (h.app U).toLinearMap (x : (X.obj U).M) y)

/-- A homotopy, on the degree-`n` pieces of the realizations. -/
def pieceMap (n : ℤ) : X.realize.complex.X n ⟶ Y.realize.complex.X (n - 1) :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (h.appPiece U n)
      naturality := fun V U a => by
        ext x
        exact Subtype.ext
          (h.naturality a ((show (X.obj V).grading n from x) : (X.obj V).M)).symm }
    (fun U r x => Subtype.ext ((h.app U).toLinearMap.map_smul _ _))⟩

/-- On sections over `U`, `h.pieceMap n` is the homotopy `h.app U`. -/
theorem coe_pieceMap (n : ℤ) (U : Cᵒᵖ) (x : (X.complex.X n).val.obj U) :
    ((Y.cElt ((h.pieceMap n).val.app U x) : (Y.obj U).grading (n - 1)) : (Y.obj U).M) =
      (h.app U).toLinearMap (X.cElt x : (X.obj U).grading n) :=
  rfl

/-- **The realization of a homotopy** of presheaves of section modules. -/
def realize : SheafOfModules.DifferentialGradedModule.Homotopy (realizeMap f) (realizeMap g) where
  app n := h.pieceMap n
  map_mul n i U x p := Y.cElt_heq (show n + i - 1 = n - 1 + i by omega)
    ((h.app U).toLinearMap.map_smul _ _)
  comm n := by
    apply SheafOfModules.hom_ext
    ext U x
    apply Y.cElt_injective
    change (f.app U).toFun ((X.cElt x : (X.obj U).grading n) : (X.obj U).M) -
        (g.app U).toFun ((X.cElt x : (X.obj U).grading n) : (X.obj U).M) =
      ((Y.cElt ((Y.complex.d (n - 1) n).val.app U ((h.pieceMap n).val.app U x)) :
          (Y.obj U).grading n) : (Y.obj U).M) +
        ((Y.cElt ((eqToHom (congrArg Y.complex.X (show n + 1 - 1 = n by omega))).val.app U
          ((h.pieceMap (n + 1)).val.app U ((X.complex.d n (n + 1)).val.app U x))) :
            (Y.obj U).grading n) : (Y.obj U).M)
    rw [Y.coe_cElt_d' (show n - 1 + 1 = n by omega), Y.coe_cElt_eqToHom (by omega),
      h.coe_pieceMap, h.coe_pieceMap, X.coe_cElt_d]
    exact (h.app U).homotopy_eq _

end Homotopy

/-- **Realization carries homotopic morphisms to homotopic morphisms.** -/
theorem realizeMap_homotopic {f g : X ⟶ Y} (h : Homotopy f g) :
    SheafOfModules.DifferentialGradedModule.Homotopic (realizeMap f) (realizeMap g) :=
  ⟨h.realize⟩

end SectionSystem

end DifferentialGradedModule

end SheafOfModules

end
