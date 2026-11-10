module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSectionAlgebraIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeTensorKFlat
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestriction

/-!
# Extension of scalars along an inverse system, computed by absolute tensor products

Let `C` be a category with the chaotic topology, `R` a commutative ring and `D` an inverse system
`Cᵒᵖ ⥤ DifferentialGradedAlgebra R`, realized as the sheaf of differential graded algebras
`systemAlgebra D` over the constant sheaf of rings. For a complex `K` of `R`-modules the sections
of the extension of scalars `K ⊗_R systemAlgebra D` over `U` are the relative tensor product
`K ⊗_R A(U)` of differential graded modules over the lifted integers, `A(U)` being the section
algebra. This file identifies them with the tensor product of `R`-modules `(⊕ₙ Kⁿ) ⊗_R D(U)`,
compatibly with the gradings, the differentials, the action of `R`, the restriction maps, the
functoriality in `K` and the unit `x ↦ x ⊗ 1`.

## Main definitions

* `Stacks.ChaoticSite.AbsoluteExtension.absBase K`: the complex `K` as a differential graded
  module over `R` in degree zero, over the base ring `R`.
* `Stacks.ChaoticSite.AbsoluteExtension.absTensor D K U`: the differential graded `D(U)`-module
  `K ⊗_R D(U)`, on the tensor product of `R`-modules `(⊕ₙ Kⁿ) ⊗_R D(U)`.
* `Stacks.ChaoticSite.AbsoluteExtension.absComparison D K U`: the homomorphism of differential
  graded `A(U)`-modules `K ⊗_R A(U) ⟶ (⊕ₙ Kⁿ) ⊗_R D(U)`, the transpose of `x ↦ x ⊗ 1`.
* `Stacks.ChaoticSite.AbsoluteExtension.absEquiv D K U`: **the identification of the sections
  `K ⊗_R A(U)` with `(⊕ₙ Kⁿ) ⊗_R D(U)`**, `x ⊗ b ↦ x ⊗ b`.

## Main results

* `absEquiv_d`, `absEquiv_smul`, `absEquiv_mem`: the identification is compatible with the
  differentials, the action of `R` and the gradings.
* `absEquiv_restr`, `absEquiv_map`, `absEquiv_unitElt`: it is compatible with the restriction
  maps, natural in `K`, and carries the unit `x ⊗ 1` to `x ⊗ 1`.

## Implementation notes

The relative tensor product `K ⊗_R A(U)` is characterized by its universal property only. The
comparison out of it is therefore the plain transpose of the unit `x ↦ x ⊗ 1` into
`(⊕ₙ Kⁿ) ⊗_R D(U)` read over `A(U)` through the identification `A(U) = D(U)` of
`Stacks.ChaoticSite.sectionAlgebraIso`; its inverse is the tensor-product lift of
`(x, a) ↦ x ⊗ a`, which is balanced over `R` because `r · 1` acts centrally on `K ⊗_R A(U)`.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Stacks.PresheafOfModules
open scoped TensorProduct

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.ChaoticSite.AbsoluteExtension

attribute [local instance] _root_.SheafOfModules.GradedAlgebra.sectionsGOne
  _root_.SheafOfModules.GradedAlgebra.sectionsGMul _root_.SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra _root_.DifferentialGradedModule.absTensorRightModule
  _root_.DifferentialGradedModule.absTensorRightScalarTower

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]

/-! ### The complex as a differential graded module over `R` -/

section Base

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- A complex of `R`-modules, as a differential graded module over `R` in degree zero, over the
base ring `R`: the direct sum `⊕ₙ Kⁿ` with the differential of the complex. -/
abbrev absBase : _root_.DifferentialGradedModule.{u, u, u}
    (_root_.DifferentialGradedAlgebra.degreeZero R R) :=
  _root_.DifferentialGradedModule.degreeZeroTotal (R := R) (S := R) K

/-- The inclusion of the degree-`j` term into `⊕ₙ Kⁿ`. -/
def lofR (j : ℤ) : K.X j →ₗ[R] (absBase K).M := DirectSum.lof R ℤ (fun n => K.X n) j

/-- The projection of `⊕ₙ Kⁿ` onto its degree-`j` term. -/
def compR (j : ℤ) : (absBase K).M →ₗ[R] K.X j where
  toFun x := (show DirectSum ℤ (fun n => K.X n) from x) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two additive maps out of a direct sum agreeing on the summands agree. -/
private theorem directSum_apply_eq_of_of {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] {γ : Type*} [AddCommMonoid γ] (f g : DirectSum ι β →+ γ)
    (h : ∀ i y, f (DirectSum.of β i y) = g (DirectSum.of β i y)) (x : DirectSum ι β) : f x = g x :=
  DFunLike.congr_fun (DirectSum.addHom_ext h) x

/-- The projection onto `Kʲ` of an element of `Kʲ` is itself. -/
theorem compR_lofR_self (j : ℤ) (k : K.X j) : compR K j (lofR K j k) = k :=
  DirectSum.of_eq_same (β := fun n => K.X n) j k

/-- The projection onto `Kʲ` of an element of `Kⁱ`, `i ≠ j`, is zero. -/
theorem compR_lofR_of_ne {i j : ℤ} (h : i ≠ j) (k : K.X i) : compR K j (lofR K i k) = 0 :=
  DirectSum.of_eq_of_ne (β := fun n => K.X n) i j k h.symm

/-- The projection of an inclusion, along an equality of degrees, is the transport along it. -/
theorem compR_lofR_eq {i j : ℤ} (h : i = j) (k : K.X i) :
    compR K j (lofR K i k) = (eqToHom (congrArg K.X h)).hom k := by
  subst h
  exact compR_lofR_self K i k

/-- Transport along an equality of degrees commutes with the projections. -/
theorem eqToHom_compR {i j : ℤ} (h : i = j) (x : (absBase K).M) :
    (eqToHom (congrArg K.X h)).hom (compR K i x) = compR K j x := by
  subst h
  rfl

/-- Projecting onto `Kʲ` and including back, on an element of `Kⁱ`. -/
theorem lofR_compR_lofR {i j : ℤ} (k : K.X i) :
    lofR K j (compR K j (lofR K i k)) = if i = j then lofR K i k else 0 := by
  split_ifs with h
  · subst h
    rw [compR_lofR_self]
  · rw [compR_lofR_of_ne K h, map_zero]

/-- An element of `⊕ₙ Kⁿ` over the lifted integers, read over `R`. -/
def toAbsBase (x : (baseModule K).M) : (absBase K).M := x

/-- An element of `⊕ₙ Kⁿ` over `R`, read over the lifted integers. -/
def ofAbsBase (x : (absBase K).M) : (baseModule K).M := x

/-- Reading over `R` and back is the identity. -/
@[simp] theorem toAbsBase_ofAbsBase (x : (absBase K).M) : toAbsBase K (ofAbsBase K x) = x := rfl

/-- Reading over the lifted integers and back is the identity. -/
@[simp] theorem ofAbsBase_toAbsBase (x : (baseModule K).M) : ofAbsBase K (toAbsBase K x) = x :=
  rfl

/-- Reading over the lifted integers is additive. -/
theorem ofAbsBase_add (x y : (absBase K).M) :
    ofAbsBase K (x + y) = ofAbsBase K x + ofAbsBase K y := rfl

/-- Reading over `R` is additive. -/
theorem toAbsBase_add (x y : (baseModule K).M) :
    toAbsBase K (x + y) = toAbsBase K x + toAbsBase K y := rfl

/-- An element of `Kʲ` in `⊕ₙ Kⁿ`, read over `R`. -/
theorem toAbsBase_baseElt (j : ℤ) (k : K.X j) : toAbsBase K (baseElt K j k) = lofR K j k := rfl

/-- An element of `Kʲ` has degree `j` in `⊕ₙ Kⁿ`. -/
theorem lofR_mem (j : ℤ) (k : K.X j) : lofR K j k ∈ (absBase K).grading j := ⟨k, rfl⟩

/-- The differential of `⊕ₙ Kⁿ` on an element of `Kʲ`. -/
theorem absBase_d_lofR (j : ℤ) (k : K.X j) :
    (absBase K).d (lofR K j k) = lofR K (j + 1) (K.d j (j + 1) k) :=
  _root_.DifferentialGradedModule.complexDifferential_lof K j k

/-- The projections commute with the differentials. -/
theorem compR_d {j j' : ℤ} (h : j + 1 = j') (x : (absBase K).M) :
    compR K j' ((absBase K).d x) = K.d j j' (compR K j x) := by
  subst h
  refine directSum_apply_eq_of_of
    ((compR K (j + 1)).toAddMonoidHom.comp (absBase K).d.toAddMonoidHom :
      (absBase K).M →+ K.X (j + 1))
    ((K.d j (j + 1)).hom.toAddMonoidHom.comp (compR K j).toAddMonoidHom)
    (fun i k => ?_) x
  change compR K (j + 1) ((absBase K).d (lofR K i k)) = K.d j (j + 1) (compR K j (lofR K i k))
  rw [absBase_d_lofR]
  by_cases hij : i = j
  · subst hij
    rw [compR_lofR_self, compR_lofR_self]
  · rw [compR_lofR_of_ne K hij, compR_lofR_of_ne K (by omega), map_zero]

/-- An element of `⊕ₙ Kⁿ` homogeneous of degree `p` is the inclusion of an element of `Kᵖ`. -/
theorem baseModule_mem_iff (p : ℤ) (x : (baseModule K).M) :
    x ∈ (baseModule K).grading p ↔ toAbsBase K x ∈ (absBase K).grading p := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩

/-- The differential of `⊕ₙ Kⁿ` does not depend on the base ring. -/
theorem baseModule_d (x : (baseModule K).M) :
    toAbsBase K ((baseModule K).d x) = (absBase K).d (toAbsBase K x) := by
  exact directSum_apply_eq_of_of ((baseModule K).d.toAddMonoidHom : (baseModule K).M →+ _)
    ((absBase K).d.toAddMonoidHom : (absBase K).M →+ (absBase K).M)
    (fun i k => (d_baseElt K i k).trans (absBase_d_lofR K i k).symm) x

/-- The right action of `R` on `⊕ₙ Kⁿ` is the scalar action. -/
theorem baseModule_op_smul (a : R) (x : (baseModule K).M) :
    toAbsBase K (@HSMul.hSMul (baseDGA R).Aᵐᵒᵖ (baseModule K).M (baseModule K).M
        (@instHSMul _ _ (baseModule K).rmodule.toSMul) (MulOpposite.op a) x) =
      a • toAbsBase K x := by
  have key : (AddMonoidHom.mk' (fun x : (baseModule K).M =>
      @HSMul.hSMul (baseDGA R).Aᵐᵒᵖ (baseModule K).M (baseModule K).M
        (@instHSMul _ _ (baseModule K).rmodule.toSMul) (MulOpposite.op a) x)
        (fun x y => @smul_add _ _ _ (baseModule K).rmodule.toDistribMulAction.toDistribSMul
          (MulOpposite.op a) x y) : (baseModule K).M →+ (baseModule K).M) =
      AddMonoidHom.mk' (fun x : (absBase K).M => a • x) (fun x y => smul_add a x y) :=
    DirectSum.addHom_ext fun i k => (op_smul_baseElt K i a k).trans
      ((lofR K i).map_smul a k)
  exact DFunLike.congr_fun key x

end Base


/-! ### The section algebras -/

section SectionAlgebra

variable (D : Cᵒᵖ ⥤ _root_.DifferentialGradedAlgebra.{u, u} R)

/-- The sheaf of differential graded algebras of the inverse system `D`, read over the underlying
sheaf of rings of the constant sheaf of commutative rings. -/
abbrev sysAlg : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) R)) :=
  systemAlgebra D

/-- The identification `A(U) → D(U)` of the section algebra with `D(U)`, as a ring
homomorphism. -/
abbrev secHom (U : Cᵒᵖ) : ((sysAlg D).sectionAlgebra U).A →+* (D.obj U).A :=
  sectionRingHom D U

/-- The inverse identification `D(U) → A(U)`. -/
abbrev secInv (U : Cᵒᵖ) : (D.obj U).A →+* ((sysAlg D).sectionAlgebra U).A :=
  (sectionRingEquiv D U).symm.toRingHom

/-- The two identifications of the section algebra are mutually inverse. -/
theorem secHom_secInv (U : Cᵒᵖ) (a : (D.obj U).A) : secHom D U (secInv D U a) = a :=
  (sectionRingEquiv D U).apply_symm_apply a

/-- The two identifications of the section algebra are mutually inverse. -/
theorem secInv_secHom (U : Cᵒᵖ) (x : ((sysAlg D).sectionAlgebra U).A) :
    secInv D U (secHom D U x) = x :=
  (sectionRingEquiv D U).symm_apply_apply x

/-- The identification of the section algebras carries the scalar `r · 1` to `r · 1`. -/
theorem secHom_structureHom (U : Cᵒᵖ) (r : R) :
    secHom D U ((structureHom (sysAlg D) U).toAlgebraHom r) = algebraMap R (D.obj U).A r := by
  change sectionRingHom D U (DirectSum.of _ 0 (r • (systemAlgebra D).one.eval U)) = _
  rw [sectionRingHom_of, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The inverse identification carries `r · 1` to the scalar `r · 1` of the section algebra. -/
theorem secInv_algebraMap (U : Cᵒᵖ) (r : R) :
    secInv D U (algebraMap R (D.obj U).A r) = (structureHom (sysAlg D) U).toAlgebraHom r := by
  rw [← secHom_structureHom, secInv_secHom]

/-- The identification of the section algebras commutes with the differentials. -/
theorem secHom_d (U : Cᵒᵖ) (x : ((sysAlg D).sectionAlgebra U).A) :
    secHom D U (((sysAlg D).sectionAlgebra U).d x) = (D.obj U).d (secHom D U x) :=
  (sectionAlgebraHom D U).map_d x

/-- The identification of the section algebras preserves the gradings. -/
theorem secHom_mem (U : Cᵒᵖ) {q : ℤ} {x : ((sysAlg D).sectionAlgebra U).A}
    (hx : x ∈ ((sysAlg D).sectionAlgebra U).grading q) : secHom D U x ∈ (D.obj U).grading q :=
  (sectionAlgebraHom D U).map_grading q x hx

/-- The inverse identification of the section algebras preserves the gradings. -/
theorem secInv_mem (U : Cᵒᵖ) {q : ℤ} {a : (D.obj U).A} (ha : a ∈ (D.obj U).grading q) :
    secInv D U a ∈ ((sysAlg D).sectionAlgebra U).grading q :=
  (sectionAlgebraInv D U).map_grading q a ha

/-- The identification of the section algebras commutes with restriction. -/
theorem secHom_restriction {U V : Cᵒᵖ} (a : V ⟶ U) (x : ((sysAlg D).sectionAlgebra V).A) :
    secHom D U (((sysAlg D).sectionRestriction a).toAlgebraHom x) =
      (D.map a).toAlgebraHom (secHom D V x) :=
  congrArg (fun φ => φ.toAlgebraHom x) (sectionAlgebraIso_hom_naturality D U a)

end SectionAlgebra

/-! ### The absolute tensor product -/

section Absolute

variable (D : Cᵒᵖ ⥤ _root_.DifferentialGradedAlgebra.{u, u} R)
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **The absolute tensor product `K ⊗_R D(U)`**, a right differential graded `D(U)`-module on
the tensor product of `R`-modules `(⊕ₙ Kⁿ) ⊗_R D(U)`. -/
abbrev absTensor (U : Cᵒᵖ) : _root_.DifferentialGradedModule.{u, u, u} (D.obj U) :=
  _root_.DifferentialGradedModule.absoluteTensor (absBase K) (D.obj U)

/-- The absolute tensor product `K ⊗_R D(U)`, read over the section algebra `A(U)`. -/
abbrev absTarget (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.{u, u, u} ((sysAlg D).sectionAlgebra U) :=
  _root_.DifferentialGradedModule.restrictScalars (sectionAlgebraIso D U).hom
    (_root_.DifferentialGradedModule.restrictBaseObj (ULift.{u} ℤ) (absTensor D K U))

/-- The pure tensor `x ⊗ a` of `(⊕ₙ Kⁿ) ⊗_R D(U)`. -/
abbrev absTmul (U : Cᵒᵖ) (x : (absBase K).M) (a : (D.obj U).A) : (absTensor D K U).M :=
  TensorProduct.tmul R x a

/-- The biadditive map `(x, b) ↦ x ⊗ b` out of `⊕ₙ Kⁿ` and `A(U)`. -/
def absPureAdd (U : Cᵒᵖ) :
    (baseModule K).M →+ (extensionBimodule (sysAlg D) U).rightModule.M →+ (absTarget D K U).M :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => absTmul D K U (toAbsBase K x) (secHom D U y))
      (fun y y' => (congrArg (absTmul D K U (toAbsBase K x)) (map_add (secHom D U) y y')).trans
        (TensorProduct.tmul_add _ _ _)))
    (fun x x' => AddMonoidHom.ext fun y =>
      TensorProduct.add_tmul (R := R) (toAbsBase K x) (toAbsBase K x') (secHom D U y))

/-- The bilinear map `(x, b) ↦ x ⊗ b` out of `⊕ₙ Kⁿ` and `A(U)`. -/
def absPureLinear (U : Cᵒᵖ) :=
  uliftBilinear (baseModule K).module (extensionBimodule (sysAlg D) U).rightModule.module
    (absTarget D K U).module (absPureAdd D K U)

/-- The bilinear map `(x, b) ↦ x ⊗ b` on a pair. -/
theorem absPureLinear_apply (U : Cᵒᵖ) (x : (baseModule K).M)
    (y : (extensionBimodule (sysAlg D) U).rightModule.M) :
    absPureLinear D K U x y = absTmul D K U (toAbsBase K x) (secHom D U y) := rfl


/-- The additive map `x ↦ x ⊗ 1`. -/
def absUnitAdd (U : Cᵒᵖ) : (baseModule K).M →+ (absTarget D K U).M :=
  AddMonoidHom.mk' (fun x => absTmul D K U (toAbsBase K x) 1)
    (fun x y => TensorProduct.add_tmul (R := R) (toAbsBase K x) (toAbsBase K y) (1 : (D.obj U).A))

/-- The unit `x ↦ x ⊗ 1`, into `(⊕ₙ Kⁿ) ⊗_R D(U)` read over `R` through `A(U)`. -/
def absUnit (U : Cᵒᵖ) :
    baseModule K ⟶
      (_root_.DifferentialGradedModule.restrictScalarsFunctor (structureHom (sysAlg D) U)).obj
        (absTarget D K U) where
  toFun := SectionSystem.uliftLinear.{u} (baseModule K).module (absTarget D K U).module
    (absUnitAdd D K U)
  map_smul x a := by
    change absTmul D K U (toAbsBase K _) 1 =
      absTmul D K U (toAbsBase K x) (1 * secHom D U ((structureHom (sysAlg D) U).toAlgebraHom a))
    rw [baseModule_op_smul, one_mul, secHom_structureHom, Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  map_grading n x hx := by
    have h :=
      _root_.DifferentialGradedModule.absTmul_mem (absBase K) (D.obj U) n 0 (toAbsBase K x) 1
        ((baseModule_mem_iff K n x).1 hx) SetLike.GradedOne.one_mem
    rw [add_zero] at h
    exact h
  map_d := by
    refine DFunLike.ext _ _ fun x => ?_
    change absTmul D K U (toAbsBase K ((baseModule K).d x)) 1 =
      _root_.DifferentialGradedModule.absTensorDifferential (absBase K) (D.obj U)
        (absTmul D K U (toAbsBase K x) 1)
    rw [baseModule_d]
    simp only [absTmul, _root_.DifferentialGradedModule.absTensorDifferential,
      LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [← map_one (algebraMap R (D.obj U).A), DifferentialGradedAlgebra.d_algebraMap,
      TensorProduct.tmul_zero, add_zero]

/-- The unit is `x ↦ x ⊗ 1`. -/
theorem absUnit_apply (U : Cᵒᵖ) (x : (baseModule K).M) :
    (absUnit D K U).toFun x = absTmul D K U (toAbsBase K x) 1 := rfl

/-- **The comparison** `K ⊗_R A(U) ⟶ (⊕ₙ Kⁿ) ⊗_R D(U)`, `x ⊗ b ↦ x ⊗ b`, a homomorphism of
differential graded `A(U)`-modules: the transpose of the unit `x ↦ x ⊗ 1`. -/
def absComparison (U : Cᵒᵖ) : extensionSections (sysAlg D) K U ⟶ absTarget D K U :=
  plainTranspose (structureHom (sysAlg D) U) (absUnit D K U)

/-- The comparison on a homogeneous pure tensor. -/
theorem absComparison_pure_homogeneous (U : Cᵒᵖ) (p : ℤ) (x : (baseModule K).grading p)
    (b : (extensionBimodule (sysAlg D) U).rightModule.M) :
    (absComparison D K U).toFun (extensionPure (sysAlg D) K U x b) =
      absTmul D K U (toAbsBase K x) (secHom D U b) := by
  refine (plainTranspose_pure (structureHom (sysAlg D) U) (absUnit D K U) p x b).trans ?_
  change absTmul D K U (toAbsBase K x) (1 * secHom D U b) = _
  rw [one_mul]

/-- **The comparison on a pure tensor**: `x ⊗ b ↦ x ⊗ b`. -/
theorem absComparison_pure (U : Cᵒᵖ) (x : (baseModule K).M)
    (b : (extensionBimodule (sysAlg D) U).rightModule.M) :
    (absComparison D K U).toFun (extensionPure (sysAlg D) K U x b) =
      absTmul D K U (toAbsBase K x) (secHom D U b) := by
  have key : (AddMonoidHom.mk' (fun x => (absComparison D K U).toFun
      (extensionPure (sysAlg D) K U x b)) (fun x y =>
        (congrArg (fun g => (absComparison D K U).toFun (g b))
          (map_add (extensionPure (sysAlg D) K U) x y)).trans
          (map_add (absComparison D K U).toFun (extensionPure (sysAlg D) K U x b)
            (extensionPure (sysAlg D) K U y b))) : (baseModule K).M →+ (absTarget D K U).M) =
      (AddMonoidHom.mk' (fun x => absTmul D K U (toAbsBase K x) (secHom D U b))
        (fun x y => TensorProduct.add_tmul _ _ _)) := by
    refine DirectSum.addHom_ext fun i k => ?_
    exact absComparison_pure_homogeneous D K U i ⟨baseElt K i k, baseElt_mem K i k⟩ b
  exact DFunLike.congr_fun key x


/-- The unit on a scalar multiple. -/
theorem unitElt_ofAbsBase_smul (U : Cᵒᵖ) (a : R) (x : (absBase K).M) :
    unitElt (sysAlg D) K U (ofAbsBase K (a • x)) =
      (sysAlg D).sectionScalarOp U a • unitElt (sysAlg D) K U (ofAbsBase K x) := by
  have h1 : ofAbsBase K (a • x) = @HSMul.hSMul (baseDGA R).Aᵐᵒᵖ (baseModule K).M (baseModule K).M
      (@instHSMul _ _ (baseModule K).rmodule.toSMul) (MulOpposite.op a) (ofAbsBase K x) :=
    (baseModule_op_smul K a (ofAbsBase K x)).symm
  rw [h1]
  exact (extensionUnit (sysAlg D) K U).map_smul (ofAbsBase K x) a

/-- A pure tensor is the unit acted on by the second factor. -/
theorem extensionPure_eq_smul_unitElt (U : Cᵒᵖ) (x : (baseModule K).M)
    (b : ((sysAlg D).sectionAlgebra U).A) :
    extensionPure (sysAlg D) K U x (bimElt (sysAlg D) U b) =
      MulOpposite.op b • unitElt (sysAlg D) K U x := by
  rw [unitElt_eq]
  exact (extensionPure_one_smul (sysAlg D) K U x b).symm

/-- The biadditive map `(x, a) ↦ x ⊗ a` out of `⊕ₙ Kⁿ` and `D(U)` into `K ⊗_R A(U)`. -/
def absInvAdd (U : Cᵒᵖ) :
    (absBase K).M →+ (D.obj U).A →+ (extensionSections (sysAlg D) K U).M :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun e => extensionPure (sysAlg D) K U (ofAbsBase K x) (bimElt (sysAlg D) U (secInv D U e)))
      (fun e e' => (congrArg (fun b => extensionPure (sysAlg D) K U (ofAbsBase K x)
          (bimElt (sysAlg D) U b)) (map_add (secInv D U) e e')).trans
        (map_add (extensionPure (sysAlg D) K U (ofAbsBase K x)) _ _)))
    (fun x x' => AddMonoidHom.ext fun e =>
      congrArg (fun g => g (bimElt (sysAlg D) U (secInv D U e)))
        (map_add (extensionPure (sysAlg D) K U) (ofAbsBase K x) (ofAbsBase K x')))

/-- The biadditive map `(x, a) ↦ x ⊗ a` on a pair. -/
theorem absInvAdd_apply (U : Cᵒᵖ) (x : (absBase K).M) (e : (D.obj U).A) :
    absInvAdd D K U x e =
      extensionPure (sysAlg D) K U (ofAbsBase K x) (bimElt (sysAlg D) U (secInv D U e)) := rfl

/-- The biadditive map `(x, a) ↦ x ⊗ a` is balanced over `R`. -/
theorem absInvAdd_smul (U : Cᵒᵖ) (a : R) (x : (absBase K).M) (e : (D.obj U).A) :
    absInvAdd D K U (a • x) e = absInvAdd D K U x (a • e) := by
  rw [absInvAdd_apply, absInvAdd_apply, extensionPure_eq_smul_unitElt,
    extensionPure_eq_smul_unitElt, unitElt_ofAbsBase_smul, Algebra.smul_def, map_mul,
    secInv_algebraMap, MulOpposite.op_mul, mul_smul]
  rfl

/-- **The inverse comparison** `(⊕ₙ Kⁿ) ⊗_R D(U) → K ⊗_R A(U)`, `x ⊗ a ↦ x ⊗ a`. -/
def absInverse (U : Cᵒᵖ) : (absTensor D K U).M →+ (extensionSections (sysAlg D) K U).M :=
  TensorProduct.liftAddHom (absInvAdd D K U) (absInvAdd_smul D K U)

/-- The inverse comparison on a pure tensor. -/
theorem absInverse_tmul (U : Cᵒᵖ) (x : (absBase K).M) (e : (D.obj U).A) :
    absInverse D K U (absTmul D K U x e) =
      extensionPure (sysAlg D) K U (ofAbsBase K x) (bimElt (sysAlg D) U (secInv D U e)) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- Two additive maps out of `K ⊗_R A(U)` agreeing on homogeneous pure tensors are equal. -/
private theorem extensionSections_apply_eq_of_pure (U : Cᵒᵖ) {P : Type*} [AddCommGroup P]
    (f g : (extensionSections (sysAlg D) K U).M →+ P)
    (h : ∀ (p q : ℤ) (x : (baseModule K).grading p)
      (y : (extensionBimodule (sysAlg D) U).rightModule.grading q),
      f (extensionPure (sysAlg D) K U x y) = g (extensionPure (sysAlg D) K U x y))
    (z : (extensionSections (sysAlg D) K U).M) : f z = g z :=
  DFunLike.congr_fun (tensorObj_addHom_ext_homogeneous _ _ f g h) z

/-- The inverse comparison is a left inverse. -/
theorem absInverse_comparison (U : Cᵒᵖ) (z : (extensionSections (sysAlg D) K U).M) :
    absInverse D K U ((absComparison D K U).toFun z) = z := by
  refine extensionSections_apply_eq_of_pure D K U
    ((absInverse D K U).comp (absComparison D K U).toFun.toAddMonoidHom) (AddMonoidHom.id _)
    (fun p q x y => ?_) z
  change absInverse D K U ((absComparison D K U).toFun (extensionPure (sysAlg D) K U x y)) =
    extensionPure (sysAlg D) K U x y
  rw [absComparison_pure, absInverse_tmul]
  exact congrArg (fun b => extensionPure (sysAlg D) K U (x : (baseModule K).M)
    (bimElt (sysAlg D) U b))
    (secInv_secHom D U (y : (extensionBimodule (sysAlg D) U).rightModule.M))

/-- The inverse comparison is a right inverse. -/
theorem absComparison_inverse (U : Cᵒᵖ) (w : (absTensor D K U).M) :
    (absComparison D K U).toFun (absInverse D K U w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul x e =>
    rw [absInverse_tmul]
    exact (absComparison_pure D K U _ _).trans (congrArg (absTmul D K U x) (secHom_secInv D U e))
  | add w w' hw hw' =>
    rw [map_add]
    exact (map_add (absComparison D K U).toFun _ _).trans (by rw [hw, hw'])

/-- **The sections `K ⊗_R A(U)` are `(⊕ₙ Kⁿ) ⊗_R D(U)`**, as abelian groups. -/
def absEquiv (U : Cᵒᵖ) : (extensionSections (sysAlg D) K U).M ≃+ (absTensor D K U).M where
  toFun z := (absComparison D K U).toFun z
  invFun := absInverse D K U
  left_inv := absInverse_comparison D K U
  right_inv := absComparison_inverse D K U
  map_add' z z' := map_add (absComparison D K U).toFun z z'

/-- The identification is the comparison. -/
theorem absEquiv_apply (U : Cᵒᵖ) (z : (extensionSections (sysAlg D) K U).M) :
    absEquiv D K U z = (absComparison D K U).toFun z := rfl

/-- The inverse identification is the inverse comparison. -/
theorem absEquiv_symm_apply (U : Cᵒᵖ) (w : (absTensor D K U).M) :
    (absEquiv D K U).symm w = absInverse D K U w := rfl

/-- The identification on a pure tensor. -/
theorem absEquiv_pure (U : Cᵒᵖ) (x : (baseModule K).M)
    (b : (extensionBimodule (sysAlg D) U).rightModule.M) :
    absEquiv D K U (extensionPure (sysAlg D) K U x b) =
      absTmul D K U (toAbsBase K x) (secHom D U b) :=
  absComparison_pure D K U x b

/-- The identification carries the unit `x ⊗ 1` to `x ⊗ 1`. -/
theorem absEquiv_unitElt (U : Cᵒᵖ) (x : (baseModule K).M) :
    absEquiv D K U (unitElt (sysAlg D) K U x) = absTmul D K U (toAbsBase K x) 1 := by
  rw [unitElt_eq, absEquiv_pure]
  exact congrArg (absTmul D K U (toAbsBase K x)) (map_one (secHom D U))

/-- The identification commutes with the differentials. -/
theorem absEquiv_d (U : Cᵒᵖ) (z : (extensionSections (sysAlg D) K U).M) :
    absEquiv D K U ((extensionSections (sysAlg D) K U).d z) =
      _root_.DifferentialGradedModule.absTensorDifferential (absBase K) (D.obj U)
        (absEquiv D K U z) :=
  DFunLike.congr_fun (absComparison D K U).map_d z

/-- The identification carries the action of `r ∈ R` through `r · 1` to the scalar action. -/
theorem absEquiv_smul (U : Cᵒᵖ) (a : R) (z : (extensionSections (sysAlg D) K U).M) :
    absEquiv D K U ((sysAlg D).sectionScalarOp U a • z) = a • absEquiv D K U z := by
  refine ((absComparison D K U).map_smul z ((sysAlg D).sectionScalar U a)).trans ?_
  change MulOpposite.op (secHom D U ((structureHom (sysAlg D) U).toAlgebraHom a)) •
    absEquiv D K U z = _
  rw [secHom_structureHom]
  induction absEquiv D K U z using TensorProduct.inductionOn with
  | tmul x e =>
    rw [_root_.DifferentialGradedModule.absTensor_smul_tmul, ← Algebra.commutes,
      ← Algebra.smul_def, TensorProduct.tmul_smul]
  | add w w' hw hw' => rw [smul_add, smul_add, hw, hw']

/-- The identification preserves the gradings. -/
theorem absEquiv_mem (U : Cᵒᵖ) {t : ℤ} {z : (extensionSections (sysAlg D) K U).M}
    (hz : z ∈ (extensionSections (sysAlg D) K U).grading t) :
    absEquiv D K U z ∈ _root_.DifferentialGradedModule.absTensorGrading (absBase K) (D.obj U) t :=
  (absComparison D K U).map_grading t z hz


/-- The restriction `(⊕ₙ Kⁿ) ⊗_R D(V) → (⊕ₙ Kⁿ) ⊗_R D(U)` along `a : V ⟶ U`, `x ⊗ e ↦ x ⊗ D(a) e`.
-/
def absRestr {U V : Cᵒᵖ} (a : V ⟶ U) : (absTensor D K V).M →ₗ[R] (absTensor D K U).M :=
  TensorProduct.map LinearMap.id (D.map a).toAlgebraHom.toLinearMap

/-- The restriction on a pure tensor. -/
theorem absRestr_tmul {U V : Cᵒᵖ} (a : V ⟶ U) (x : (absBase K).M) (e : (D.obj V).A) :
    absRestr D K a (absTmul D K V x e) = absTmul D K U x ((D.map a).toAlgebraHom e) := rfl

/-- The restriction `K ⊗_R A(V) → K ⊗_R A(U)` along `a : V ⟶ U`, as a map of the underlying
groups. -/
def secRestr {U V : Cᵒᵖ} (a : V ⟶ U) (z : (extensionSections (sysAlg D) K V).M) :
    (extensionSections (sysAlg D) K U).M :=
  (extensionRestr (sysAlg D) K a).toFun z

/-- **The identification commutes with restriction.** -/
theorem absEquiv_restr {U V : Cᵒᵖ} (a : V ⟶ U) (z : (extensionSections (sysAlg D) K V).M) :
    absEquiv D K U (secRestr D K a z) = absRestr D K a (absEquiv D K V z) := by
  refine extensionSections_apply_eq_of_pure D K V
    ((absEquiv D K U).toAddMonoidHom.comp (extensionRestr (sysAlg D) K a).toFun.toAddMonoidHom)
    ((absRestr D K a).toAddMonoidHom.comp (absEquiv D K V).toAddMonoidHom)
    (fun p q x y => ?_) z
  change absEquiv D K U ((extensionRestr (sysAlg D) K a).toFun
      (extensionPure (sysAlg D) K V x y)) =
    absRestr D K a (absEquiv D K V (extensionPure (sysAlg D) K V x y))
  rw [extensionRestr_pure (sysAlg D) K a p x, absEquiv_pure, absEquiv_pure, absRestr_tmul]
  exact congrArg (absTmul D K U _) (secHom_restriction D a _)

variable {K} in
/-- A cochain map, on `(⊕ₙ Kⁿ) ⊗_R D(U)`. -/
def absMap {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (U : Cᵒᵖ) :
    (absTensor D K U).M →ₗ[R] (absTensor D L U).M :=
  TensorProduct.map (DirectSum.lmap fun n => (g.f n).hom) LinearMap.id

variable {K} in
/-- A cochain map, on a pure tensor. -/
theorem absMap_tmul {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (U : Cᵒᵖ)
    (x : (absBase K).M) (e : (D.obj U).A) :
    absMap D g U (absTmul D K U x e) =
      absTmul D L U (DirectSum.lmap (fun n => (g.f n).hom) x) e := rfl

variable {K} in
/-- **The identification is natural in the complex.** -/
theorem absEquiv_map {L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (U : Cᵒᵖ)
    (z : (extensionSections (sysAlg D) K U).M) :
    absEquiv D L U ((extensionSectionsMap (sysAlg D) g U).toFun z) =
      absMap D g U (absEquiv D K U z) := by
  refine extensionSections_apply_eq_of_pure D K U
    ((absEquiv D L U).toAddMonoidHom.comp
      (extensionSectionsMap (sysAlg D) g U).toFun.toAddMonoidHom)
    ((absMap D g U).toAddMonoidHom.comp (absEquiv D K U).toAddMonoidHom) (fun p q x y => ?_) z
  change absEquiv D L U ((extensionSectionsMap (sysAlg D) g U).toFun
      (extensionPure (sysAlg D) K U x y)) =
    absMap D g U (absEquiv D K U (extensionPure (sysAlg D) K U x y))
  rw [extensionSectionsMap_pure, absEquiv_pure, absEquiv_pure, absMap_tmul]
  rfl

/-- The identification carries the pure tensor of `x` and `D(U) ∋ e` back from `x ⊗ e`. -/
theorem absEquiv_symm_tmul (U : Cᵒᵖ) (x : (absBase K).M) (e : (D.obj U).A) :
    (absEquiv D K U).symm (absTmul D K U x e) =
      extensionPure (sysAlg D) K U (ofAbsBase K x) (bimElt (sysAlg D) U (secInv D U e)) :=
  absInverse_tmul D K U x e

/-- The pure tensor of homogeneous elements is homogeneous. -/
theorem absEquiv_symm_tmul_mem (U : Cᵒᵖ) {p q t : ℤ} (h : p + q = t) {x : (absBase K).M}
    (hx : x ∈ (absBase K).grading p) {e : (D.obj U).A} (he : e ∈ (D.obj U).grading q) :
    (absEquiv D K U).symm (absTmul D K U x e) ∈ (extensionSections (sysAlg D) K U).grading t := by
  subst h
  rw [absEquiv_symm_tmul]
  exact (tensorPure (extensionBimodule (sysAlg D) U) (baseModule K)).map_grading p q
    ⟨ofAbsBase K x, (baseModule_mem_iff K p _).2 hx⟩ ⟨_, secInv_mem D U he⟩

end Absolute

end Stacks.ChaoticSite.AbsoluteExtension

end
