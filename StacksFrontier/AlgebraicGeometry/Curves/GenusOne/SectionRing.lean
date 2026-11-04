module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedSectionRingMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.Basic

/-!
# The section ring of an invertible module over a scheme over a field, as a graded algebra

Let `X` be a scheme over a field `k` and `L` an invertible `𝒪_X`-module. The
section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV is a `k`-algebra through its
degree-zero part (`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra`),
and its grading by the summands is then a grading by `k`-submodules. This file
records that structure, so that the graded-algebra theory of Mathlib (`GradedAlgebra`) applies to
`Γ_*(X, L)` over `k`.

## Main definitions

* `AlgebraicGeometry.GenusOne.gradingK`: the `n`-th summand as a `k`-submodule.

## Main results

* `AlgebraicGeometry.GenusOne.degreeZeroHom_mul_of`: a function acts on a homogeneous element of
  any degree by composing with the corresponding endomorphism of the monoidal unit.
* `AlgebraicGeometry.GenusOne.gradedAlgebra`: the `k`-submodules grade the section ring.

## Implementation notes

The `k`-submodule `gradingK L k n` has the same carrier as the additive subgroup
`Stacks.AmpleFiniteAvoidance.grading L n` that the `Proj` constructions of this repository are
stated for, so the two gradings have the same homogeneous elements and the decomposition is
transported without change.
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open Stacks.GradedSections (powSections sectionRing mul mulMap)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.GradedSectionRingMap (degreeZeroHom)

open scoped DirectSum

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **A degree-zero element times a homogeneous element is their composite**, in every degree: the
product in the other order is `a ≫ mulMap s 0 = a ≫ s` by definition, and the ring is
commutative. -/
theorem of_zero_mul_of (a : powSections L 0) {m : ℕ} (s : powSections L m) :
    DirectSum.of (powSections L) 0 a * DirectSum.of (powSections L) m s =
      DirectSum.of (powSections L) m (a ≫ s) := by
  rw [mul_comm, Stacks.SectionProduct.of_mul_of L m 0 s a]
  rfl

/-- **A function acts on a homogeneous element of any degree by scaling.** -/
theorem degreeZeroHom_mul_of (r : Γ(X, ⊤)) {m : ℕ} (s : powSections L m) :
    degreeZeroHom L r * DirectSum.of (powSections L) m s =
      DirectSum.of (powSections L) m
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm r ≫ s) :=
  of_zero_mul_of L _ s

/-- The global section of a homogeneous element scaled by a function is the scaled global
section. -/
theorem globalSection_unitScalarEquiv_symm_comp (r : Γ(X, ⊤)) {m : ℕ} (s : powSections L m) :
    globalSection X (natTensorPow L m)
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm r ≫ s) =
      r • globalSection X (natTensorPow L m) s := by
  have h1 : Stacks.SectionRingGeometric.unitScalar X
      ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm r) = r :=
    (Stacks.SectionRingGeometric.unitScalarEquiv X).apply_symm_apply r
  show Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ _ =
    r • Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ s
  rw [Stacks.SectionRingGeometric.globalSection_unitComp, h1]

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (baseRingHom)

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra

/-- The scalar action of `k` on a homogeneous element of `Γ_*(X, L)`, for the `k`-algebra
structure `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra`. -/
theorem smul_of (c : k) {m : ℕ} (s : powSections L m) :
    (c • DirectSum.of (powSections L) m s : sectionRing L) =
      DirectSum.of (powSections L) m
        ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm (baseRingHom k X c) ≫ s) := by
  rw [Algebra.smul_def, Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.algebraMap_eq]
  exact of_zero_mul_of L _ s

/-- **The `n`-th summand of `Γ_*(X, L)`, as a `k`-submodule.** Its carrier is that of
`Stacks.AmpleFiniteAvoidance.grading L n`. -/
def gradingK (n : ℕ) : Submodule k (sectionRing L) where
  toAddSubmonoid := (Stacks.AmpleFiniteAvoidance.grading L n).toAddSubmonoid
  smul_mem' c a ha := by
    obtain ⟨s, rfl⟩ := ha
    rw [smul_of]
    exact Stacks.ExternalGrading.of_mem_summand n _

/-- An element of `Γ_*(X, L)` lies in `gradingK L k n` if and only if it lies in
`Stacks.AmpleFiniteAvoidance.grading L n`. -/
theorem mem_gradingK_iff {n : ℕ} {a : sectionRing L} :
    a ∈ gradingK L k n ↔ a ∈ Stacks.AmpleFiniteAvoidance.grading L n := Iff.rfl

/-- The `k`-submodules are a graded monoid. -/
instance gradedMonoid : SetLike.GradedMonoid (gradingK L k) where
  one_mem := SetLike.GradedOne.one_mem (A := Stacks.AmpleFiniteAvoidance.grading L)
  mul_mem i j a b ha hb :=
    SetLike.GradedMul.mul_mem (A := Stacks.AmpleFiniteAvoidance.grading L) ha hb

/-- **The `k`-submodules grade `Γ_*(X, L)`.** -/
noncomputable instance gradedAlgebra : GradedAlgebra (gradingK L k) where
  toGradedMonoid := gradedMonoid L k
  toDecomposition := (show DirectSum.IsInternal (gradingK L k) from
    DirectSum.Decomposition.isInternal (Stacks.AmpleFiniteAvoidance.grading L)).chooseDecomposition

end AlgebraicGeometry.GenusOne

end
