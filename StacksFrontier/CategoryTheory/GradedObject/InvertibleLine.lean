module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.CategoryTheory.GradedObject.KunnethIso
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# A line concentrated in one degree is an invertible graded vector space

Let `F` be a field and `V` a `ℤ`-graded `F`-vector space, with the monoidal structure of Stacks,
Homology, Example 0FFX. If `V` is one dimensional in a single degree `n` and zero in all other
degrees, then `V` is invertible (Stacks 0FFN), with inverse the dual line `(Vⁿ)^∨` placed in
degree `-n`. This is the converse of
`CategoryTheory.GradedObject.Monoidal.exists_finrank_eq_one_of_isInvertible`.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.concentratedGrading`: the grading of a module
  concentrated in one degree, with its decomposition `concentratedDecomposition`.

## Main results

* `CategoryTheory.GradedObject.Monoidal.isInvertible_of_finrank_eq_one`: a graded vector space
  which is a line in one degree and zero elsewhere is invertible.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory DirectSum
open scoped TensorProduct

universe w

section Concentrated

variable {R : Type w} [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]

/-- The grading of `M` concentrated in degree `n`: `M` in degree `n`, `0` elsewhere. -/
def concentratedGrading (n : ℤ) : ℤ → Submodule R M :=
  fun p ↦ if p = n then ⊤ else ⊥

/-- The grading concentrated in degree `n` is all of `M` in degree `n`. -/
theorem concentratedGrading_self (n : ℤ) : concentratedGrading (R := R) M n n = ⊤ := by
  simp [concentratedGrading]

/-- The grading concentrated in degree `n` is zero in every degree `p ≠ n`. -/
theorem concentratedGrading_of_ne {n p : ℤ} (h : p ≠ n) :
    concentratedGrading (R := R) M n p = ⊥ := by
  simp [concentratedGrading, h]

/-- Every element of `M` lies in degree `n` of the grading concentrated in degree `n`. -/
theorem mem_concentratedGrading_self (n : ℤ) (x : M) : x ∈ concentratedGrading (R := R) M n n := by
  rw [concentratedGrading_self]
  trivial

/-- An element of degree `p ≠ n` for the grading concentrated in degree `n` is zero. -/
theorem eq_zero_of_mem_concentratedGrading {n p : ℤ} (h : p ≠ n) {x : M}
    (hx : x ∈ concentratedGrading (R := R) M n p) : x = 0 := by
  rwa [concentratedGrading_of_ne M h, Submodule.mem_bot] at hx

/-- `M ⟶ ⨁ₚ Mₚ`, `x ↦ x` in degree `n`, for the grading concentrated in degree `n`. -/
def toConcentrated (n : ℤ) : M →ₗ[R] ⨁ p, concentratedGrading (R := R) M n p :=
  DirectSum.lof R ℤ (fun p ↦ concentratedGrading (R := R) M n p) n ∘ₗ
    LinearMap.id.codRestrict _ (mem_concentratedGrading_self M n)

/-- The decomposition of `M` for the grading concentrated in degree `n`: `x ↦ x` in degree `n`. -/
@[instance_reducible]
def concentratedDecomposition (n : ℤ) : Decomposition (concentratedGrading (R := R) M n) where
  decompose' := toConcentrated M n
  left_inv x := by
    simp [toConcentrated, DirectSum.lof_eq_of, DirectSum.coeAddMonoidHom_of]
  right_inv y := by
    refine DFunLike.congr_fun (f := (toConcentrated M n).toAddMonoidHom.comp
      (DirectSum.coeAddMonoidHom _)) (g := AddMonoidHom.id _)
      (DirectSum.addHom_ext fun p z ↦ ?_) y
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply,
      LinearMap.toAddMonoidHom_coe]
    by_cases hp : p = n
    · subst hp
      simp only [toConcentrated, LinearMap.coe_comp, Function.comp_apply, DirectSum.lof_eq_of]
      congr 1
    · obtain rfl : z = 0 := Subtype.ext (eq_zero_of_mem_concentratedGrading M hp z.2)
      simp

end Concentrated

section Line

variable {R : Type w} [CommRing R]

/-- The graded module concentrated in degree `n` has no nonzero element in degree `p ≠ n`. -/
theorem subsingleton_concentratedGrading (M : Type w) [AddCommGroup M] [Module R M] {n p : ℤ}
    (h : p ≠ n) : Subsingleton (concentratedGrading (R := R) M n p) :=
  ⟨fun x y ↦ Subtype.ext ((eq_zero_of_mem_concentratedGrading M h x.2).trans
    (eq_zero_of_mem_concentratedGrading M h y.2).symm)⟩

/-- **A graded module zero outside degree `n` is `Vⁿ` concentrated in degree `n`.** -/
def isoGradedModuleConcentrated (V : GradedObject ℤ (ModuleCat.{w} R)) (n : ℤ)
    (hz : ∀ m, m ≠ n → IsZero (V m)) :
    V ≅ gradedModule (concentratedGrading (R := R) (V n) n) :=
  GradedObject.isoMk _ _ fun k ↦
    if h : k = n then
      eqToIso (congrArg V h) ≪≫ (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _
        (by rw [h, concentratedGrading_self]))).toModuleIso
    else
      haveI := subsingleton_concentratedGrading (R := R) (V n) h
      (hz k h).iso (ModuleCat.isZero_of_subsingleton _)

/-- **The graded module `R` concentrated in degree `0` is the unit `𝟙`.** -/
def isoTensorUnitConcentrated :
    gradedModule (concentratedGrading (R := R) R 0) ≅ 𝟙_ (GradedObject ℤ (ModuleCat.{w} R)) :=
  GradedObject.isoMk _ _ fun k ↦
    if h : k = 0 then
      (LinearEquiv.ofEq _ _ (by rw [h, concentratedGrading_self])).toModuleIso ≪≫
        Submodule.topEquiv.toModuleIso ≪≫
          (GradedObject.singleObjApplyIsoOfEq (0 : ℤ) (𝟙_ (ModuleCat.{w} R)) k h).symm
    else
      haveI := subsingleton_concentratedGrading (R := R) R h
      (ModuleCat.isZero_of_subsingleton _).iso (isInitialTensorUnitApply k h).isZero

end Line

section Field

variable {F : Type w} [Field F]

/-- The contraction `L ⊗ L^∨ → F` of a line is bijective. -/
theorem contractRight_bijective (L : Type w) [AddCommGroup L] [Module F L]
    (hL : Module.finrank F L = 1) : Function.Bijective (contractRight F L) := by
  have : Module.Finite F L := Module.finite_of_finrank_eq_succ hL
  have : Nontrivial L := Module.nontrivial_of_finrank_eq_succ hL
  obtain ⟨v, hv⟩ := exists_ne (0 : L)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F hv
  have hsurj : Function.Surjective (contractRight F L) := fun c ↦
    ⟨v ⊗ₜ (c • f), by simp [hf]⟩
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hsurj, hsurj⟩
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, hL, Module.finrank_self]

variable (V : GradedObject ℤ (ModuleCat.{w} F)) (n : ℤ)

/-- The contraction `Vⁿ ⊗ (Vⁿ)^∨ → F` maps the summands of the concentrated gradings in degrees
`n`, `-n` into `F` concentrated in degree `0`. -/
theorem contractRight_mem_concentratedGrading (p q : ℤ) (a : V n) (b : Module.Dual F (V n))
    (ha : a ∈ concentratedGrading (R := F) (V n) n p)
    (hb : b ∈ concentratedGrading (R := F) (Module.Dual F (V n)) (-n) q) :
    contractRight F (V n) (a ⊗ₜ b) ∈ concentratedGrading (R := F) F 0 (p + q) := by
  by_cases hp : p = n
  · by_cases hq : q = -n
    · rw [show p + q = 0 by omega]
      exact mem_concentratedGrading_self F 0 _
    · simp [eq_zero_of_mem_concentratedGrading _ hq hb]
  · simp [eq_zero_of_mem_concentratedGrading _ hp ha]

variable {V n}

/-- **The inverse of a line in degree `n`**: the dual line in degree `-n`. -/
def hasInverseOfFinrankEqOne (hV : Module.finrank F (V n) = 1)
    (hz : ∀ m, m ≠ n → IsZero (V m)) : HasInverse V :=
  letI := concentratedDecomposition (R := F) (V n) n
  letI := concentratedDecomposition (R := F) (Module.Dual F (V n)) (-n)
  letI := concentratedDecomposition (R := F) F 0
  have isoLeft : V ⊗ gradedModule (concentratedGrading (R := F) (Module.Dual F (V n)) (-n)) ≅
      𝟙_ _ :=
    (isoGradedModuleConcentrated V n hz ⊗ᵢ Iso.refl _) ≪≫
      kunnethIso _ _ _ (contractRight F (V n)) (contractRight_mem_concentratedGrading V n)
        (contractRight_bijective _ hV) ≪≫ isoTensorUnitConcentrated
  { inv := gradedModule (concentratedGrading (R := F) (Module.Dual F (V n)) (-n))
    isoLeft := isoLeft
    isoRight := β_ _ _ ≪≫ isoLeft }

/-- **A line concentrated in one degree is invertible** (Stacks 0FFN): if `dim_F Vⁿ = 1` and
`Vᵐ = 0` for `m ≠ n`, then `V` is an invertible graded vector space. The converse is
`CategoryTheory.GradedObject.Monoidal.exists_finrank_eq_one_of_isInvertible`. -/
theorem isInvertible_of_finrank_eq_one (hV : Module.finrank F (V n) = 1)
    (hz : ∀ m, m ≠ n → IsZero (V m)) : IsInvertible V :=
  ⟨hasInverseOfFinrankEqOne hV hz⟩

end Field

end CategoryTheory.GradedObject.Monoidal

end
