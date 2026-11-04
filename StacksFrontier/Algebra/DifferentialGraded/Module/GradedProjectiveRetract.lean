module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGenerator
public import StacksFrontier.Algebra.Homology.DifferentialGraded.GradedProjective

/-! # Graded projective modules with zero differential are retracts of sums of shifts

Let `(A, d)` be a differential graded algebra over a commutative ring `R` which is concentrated
in degree zero, so that `d_A = 0`, and let `P` be a right differential graded `A`-module whose
differential vanishes and which is *projective as a graded `A`-module*
([Stacks, Tag 09K0], `Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`). This file
shows that the class of `P` in `D(A, d)` is a **retract of a direct sum of shifts of `A`**.

The argument is the one that defines graded projectivity: the free graded module on the
homogeneous elements of `P` surjects onto `P`, and graded projectivity splits that surjection.
What makes the splitting a homomorphism of *differential* graded modules — and not merely of
graded modules, which is all that graded projectivity gives — is that both modules have zero
differential: the differential of `⨁ᵢ A[kᵢ]` is `± d_A` on each summand, so it vanishes with
`d_A`, and then every graded homomorphism between the two is automatically a chain map.

## Main definitions

* `DifferentialGradedModule.smulRightHom`: right multiplication by an element of a right
  differential graded module, as a map of right `A`-modules out of the algebra.
* `DifferentialGradedModule.homOfHomogeneous`: the homomorphism `A[k] ⟶ P` attached to a
  homogeneous element of degree `-k` of a module with zero differential.
* `DifferentialGradedModule.freeCoverHom`: the homomorphism `⨁ᵢ A[kᵢ] ⟶ P` attached to a family
  of homogeneous elements of such a module.

## Main results

* `DifferentialGradedModule.surjective_freeCoverHom`: the cover attached to a family of
  homogeneous elements realizing every homogeneous element of `P` is surjective.
* `DifferentialGradedModule.exists_section_freeCoverHom_of_isProjectiveAsGradedModule`: for `P`
  projective as a graded module the cover admits a section *as a homomorphism of differential
  graded modules*.
* `DifferentialGradedModule.exists_retract_coproduct_shift_q_regularModule_of_isProjective`:
  **the bridge**. The class in `D(A, d)` of a graded projective differential graded module with
  zero differential is a retract of a direct sum of shifts of the regular module.

## Implementation notes

*Why the differential has to vanish.* Graded projectivity is a property of the underlying graded
module, and the section it produces is a graded homomorphism, with no compatibility with the
differentials; that is exactly the content of [Stacks, Tag 09K0], which concludes only that a
surjection onto a graded projective module is an *admissible* epimorphism, i.e. split after the
differentials are forgotten. A graded splitting is a splitting in `D(A, d)` only when there is
nothing for it to be compatible with, which is the hypothesis `P.d = 0` here (together with
`d_A = 0`, which follows from `A` being concentrated in degree zero). Without it the statement is
false: over `A = k[x]/(x²)` in degree zero the module `P = (A --x--> A)` has free terms, so it is
graded projective, while `H^0(P) = (x) ≅ k` is not a projective `A`-module and therefore is not a
direct summand of the cohomology `⨁ᵢ A` of any direct sum of shifts of `A`; so `P` is not a
retract of one in `D(A, d)`.

*The cover.* The index set is `Σ n : ℤ, P^n`, one cell for each homogeneous element, and the cell
of an element of degree `n` is the shift `A[-n]`, mapping to `P` by right multiplication by that
element. This is the "bare cell" half of the native cover of [Stacks, Tag 09KN]: there the cells
are two-generator modules, needed because a homogeneous element of a general module is not a
cocycle, and bare cells `A[k]` are added only for the cocycles. With `P.d = 0` every homogeneous
element is a cocycle, so the bare cells alone cover, and the cover is a direct sum of shifts on
the nose rather than an extension of one by another.

*Universes.* Single-universe throughout, as in the rest of this chapter's differential graded
interface (Tag 09JJ): the base ring, the algebra and the modules live in one universe `u`, and
the index type of a direct sum is in `Type u`, which is where `D(A, d)` has direct sums.

## References

* [Stacks Project, Tag 09K0](https://stacks.math.columbia.edu/tag/09K0), graded projectivity and
  the splitting it supplies.
* [Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN), the native cover of a
  general differential graded module.
* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL) for the shift `M[k]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Homomorphisms out of a shift of the regular module -/

/-- Right multiplication by a fixed element of a right differential graded module, as a map of
right `A`-modules out of the algebra. -/
def smulRightHom {P : DifferentialGradedModule.{u, u, u} A} (y : P.M) :
    A.A →ₗ[MulOpposite A.A] P.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • y = c • (MulOpposite.op a • y)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

/-- `smulRightHom y` sends `a` to `a • y`, the right action of `a` on `y`. -/
@[simp] theorem smulRightHom_apply {P : DifferentialGradedModule.{u, u, u} A} (y : P.M)
    (a : A.A) : smulRightHom y a = MulOpposite.op a • y := rfl

/-- **The homomorphism `A[k] ⟶ P` attached to a homogeneous element of degree `-k`**, for an
algebra concentrated in degree zero and a module with vanishing differential: right
multiplication by that element. -/
def homOfHomogeneous (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0) (k : ℤ) {y : P.M}
    (hy : y ∈ P.grading (-k)) : shift (regularModule A) k ⟶ P where
  toFun := (smulRightHom y).restrictScalars R
  map_smul x a := (smulRightHom y).map_smul (MulOpposite.op a) x
  map_grading n x hx := by
    have hx' : (x : A.A) ∈ A.grading (n + k) := hx
    have hm := P.smul_mem (-k) (n + k) y x hy hx'
    rwa [show -k + (n + k) = n from by ring] at hm
  map_d := by
    refine LinearMap.ext fun a => ?_
    have h1 : (shift (regularModule A) k).d a = 0 := by
      rw [shift_d, LinearMap.smul_apply, Units.smul_def,
        show (regularModule A).d a = A.d a from rfl, A.d_eq_zero_of_grading_eq_bot hA a,
        smul_zero]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, map_zero, hPd, LinearMap.zero_apply]

/-- The homomorphism `homOfHomogeneous hA hPd k hy` sends `a` to `a • y`. -/
@[simp] theorem homOfHomogeneous_apply (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0) (k : ℤ) {y : P.M}
    (hy : y ∈ P.grading (-k)) (a : A.A) :
    (homOfHomogeneous hA hPd k hy).toFun a = MulOpposite.op a • y := rfl

/-! ### The free cover of a module with zero differential -/

/-- **The homomorphism `⨁ᵢ A[kᵢ] ⟶ P` attached to a family of homogeneous elements** of a module
with vanishing differential, over an algebra concentrated in degree zero: on the `i`-th summand it
is right multiplication by `yᵢ`, which is homogeneous of degree `-kᵢ`. -/
def freeCoverHom (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (y : ι → P.M)
    (hy : ∀ i, y i ∈ P.grading (-(k i))) :
    directSumObj (fun i => shift (regularModule A) (k i)) ⟶ P :=
  directSumDesc _ fun i => homOfHomogeneous hA hPd (k i) (hy i)

/-- **A cover whose index set realizes every homogeneous element is surjective**: such an element
is the image of the unit of its own summand, and every element of `P` is a finite sum of
homogeneous ones. -/
theorem surjective_freeCoverHom (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (y : ι → P.M)
    (hy : ∀ i, y i ∈ P.grading (-(k i)))
    (hcov : ∀ (n : ℤ) (z : P.M), z ∈ P.grading n → ∃ i, y i = z) :
    Function.Surjective (freeCoverHom hA hPd k y hy).toFun := by
  have hgen : ∀ (i : ι), ∃ w, (freeCoverHom hA hPd k y hy).toFun w = y i := by
    intro i
    refine ⟨DirectSum.lof R ι (fun j => (shift (regularModule A) (k j)).M) i (1 : A.A), ?_⟩
    rw [show (freeCoverHom hA hPd k y hy).toFun = directSumDescLinear _
      (fun j => homOfHomogeneous hA hPd (k j) (hy j)) from rfl, directSumDescLinear_lof,
      homOfHomogeneous_apply]
    rw [MulOpposite.op_one, one_smul]
  intro z
  induction z using DirectSum.Decomposition.inductionOn P.grading with
  | zero => exact ⟨0, map_zero _⟩
  | @homogeneous n z =>
      obtain ⟨i, hi⟩ := hcov n (z : P.M) z.2
      obtain ⟨w, hw⟩ := hgen i
      exact ⟨w, hw.trans hi⟩
  | add z z' hz hz' =>
      obtain ⟨w, hw⟩ := hz
      obtain ⟨w', hw'⟩ := hz'
      exact ⟨w + w', by rw [map_add, hw, hw']⟩

/-! ### Splitting the cover -/

/-- The differential of a direct sum of shifts of the regular module vanishes when the algebra is
concentrated in degree zero. -/
theorem d_directSumObj_shift_regularModule_eq_zero
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    ∀ x : (directSumObj (fun i => shift (regularModule A) (k i))).M,
      (directSumObj (fun i => shift (regularModule A) (k i))).d x = 0 := by
  have h : ∀ x : ⨁ i : ι, (shift (regularModule A) (k i)).M,
      directSumD (fun i => shift (regularModule A) (k i)) x = 0 := fun x =>
    DirectSum.ext fun j => by
      rw [directSumD_apply, DirectSum.zero_apply, shift_d, LinearMap.smul_apply, Units.smul_def,
        show (regularModule A).d (x j) = A.d (x j) from rfl,
        A.d_eq_zero_of_grading_eq_bot hA (x j), smul_zero]
  exact h

/-- **The cover of a graded projective module with zero differential splits in `Mod_(A, d)`.**
Graded projectivity ([Stacks, Tag 09K0]) splits the surjection as a homomorphism of graded
modules, and that splitting commutes with the differentials for the trivial reason that both of
them are zero. -/
theorem exists_section_freeCoverHom_of_isProjectiveAsGradedModule
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0)
    (hproj : Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module P))
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (y : ι → P.M)
    (hy : ∀ i, y i ∈ P.grading (-(k i)))
    (hcov : ∀ (n : ℤ) (z : P.M), z ∈ P.grading n → ∃ i, y i = z) :
    ∃ s : P ⟶ directSumObj (fun i => shift (regularModule A) (k i)),
      s ≫ freeCoverHom hA hPd k y hy = 𝟙 P := by
  have hlaw := Unbundled.module_isLawful (directSumObj (fun i => shift (regularModule A) (k i)))
  obtain ⟨σ, hσ⟩ := hproj.2
    (Unbundled.module (directSumObj (fun i => shift (regularModule A) (k i))))
    ⟨hlaw.isInternal, hlaw.grading_smul⟩
    { toFun := GradedHom.opLinearMap (freeCoverHom hA hPd k y hy).toGradedHom
      map_grading := (freeCoverHom hA hPd k y hy).map_grading }
    (surjective_freeCoverHom hA hPd k y hy hcov)
  refine ⟨{ toFun := Unbundled.restrictR
              (N := Unbundled.module (directSumObj (fun i => shift (regularModule A) (k i))))
              σ.toFun
            map_smul := fun x a => σ.toFun.map_smul (MulOpposite.op a) x
            map_grading := σ.map_grading
            map_d := ?_ }, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hPd, LinearMap.zero_apply, map_zero]
    exact (d_directSumObj_shift_regularModule_eq_zero hA k _).symm
  · refine Hom.ext (LinearMap.ext fun x => ?_)
    exact hσ x

/-! ### The retract in the derived category -/

/-- **The bridge: a graded projective differential graded module with zero differential is a
retract, in `D(A, d)`, of a direct sum of shifts of the regular module.** The module is a retract
of the free graded module on its homogeneous elements already in `Mod_(A, d)`, by
`DifferentialGradedModule.exists_section_freeCoverHom_of_isProjectiveAsGradedModule`, and the
localization functor carries that retraction to `D(A, d)`, where the free module is the direct
sum of the shifts of the regular module it is built from.

This is the comparison between graded projectivity ([Stacks, Tag 09K0]) and the sums of shifts of
`A` which [Stacks, Tag 09SB] needs. See the implementation notes for why the hypothesis `P.d = 0`
cannot be dropped. -/
theorem exists_retract_coproduct_shift_q_regularModule_of_isProjective
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    {P : DifferentialGradedModule.{u, u, u} A} (hPd : P.d = 0)
    (hproj : Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module P)) :
    ∃ (ι : Type u) (k : ι → ℤ),
      Nonempty (Retract ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
        (∐ fun i => (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
          (regularModule A))⟦k i⟧))) := by
  classical
  set Q := toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q
  refine ⟨Σ n : ℤ, (P.grading n), fun c => -c.1, ?_⟩
  obtain ⟨s, hs⟩ := exists_section_freeCoverHom_of_isProjectiveAsGradedModule hA hPd hproj
    (fun c : Σ n : ℤ, (P.grading n) => -c.1) (fun c => (c.2 : P.M))
    (fun c => mem_grading_congr (neg_neg c.1).symm c.2.2)
    (fun n z hz => ⟨⟨n, ⟨z, hz⟩⟩, rfl⟩)
  refine ⟨Retract.trans
    { i := Q.map s
      r := Q.map (freeCoverHom hA hPd _ _ _)
      retract := by rw [← Q.map_comp, hs, Q.map_id] }
    (Retract.ofIso (Q.mapIso (directSumObjIsoSigma _) ≪≫ PreservesCoproduct.iso Q _ ≪≫
      Limits.Sigma.mapIso fun c => (Q.commShiftIso (-c.1)).app (regularModule A)))⟩

end DifferentialGradedModule

end
