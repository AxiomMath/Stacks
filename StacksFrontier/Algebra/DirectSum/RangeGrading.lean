module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module

/-!
# The tautological grading of a direct sum

A direct sum `⨁ i, V i` of `R`-modules carries an evident internal grading: its degree-`i` piece
is the range of the inclusion `DirectSum.lof R ι V i`. This file provides that family of
submodules, the `DirectSum.Decomposition` it defines, and the linear equivalence identifying
each piece with the corresponding summand.

## Main definitions

* `DirectSum.rangeGrading`: the degree-`i` piece, as a submodule of `⨁ i, V i`.
* `DirectSum.rangeGradingDecomposition`: the direct-sum decomposition it defines.
* `DirectSum.rangeGradingEquiv`: the identification of the degree-`i` piece with `V i`.

## Main results

* `DirectSum.mem_rangeGrading`: membership in the degree-`i` piece means being `of V i a` for
  some `a`.
* `DirectSum.rangeGradingEquiv_eq_of_coe_eq`: `rangeGradingEquiv` reads off the summand
  representing a homogeneous element.
* `DirectSum.of_eq_of_heq`: two inclusions of heterogeneously equal elements agree.
* `DirectSum.of_sub_smul`: the inclusion of a summand commutes with `a - r • b`.
-/

@[expose] public section

namespace DirectSum

universe u

variable (R : Type u) [Semiring R] {ι : Type*} (V : ι → Type*) [DecidableEq ι]
  [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]

/-- The degree-`i` piece of the tautological grading of `⨁ i, V i`: the range of the inclusion of
the `i`-th summand. -/
abbrev rangeGrading (i : ι) : Submodule R (DirectSum ι V) :=
  LinearMap.range (DirectSum.lof R ι V i)

/-- An element of `⨁ i, V i` lies in the degree-`i` piece exactly when it is the image of an
element of `V i`. -/
theorem mem_rangeGrading (i : ι) (z : DirectSum ι V) :
    z ∈ rangeGrading R V i ↔ ∃ a : V i, z = DirectSum.of V i a := by
  simp only [LinearMap.mem_range, DirectSum.lof_eq_of, eq_comm]

/-- The ranges of the inclusions of the summands form an internal grading of `⨁ i, V i`. -/
@[instance_reducible]
noncomputable def rangeGradingDecomposition : DirectSum.Decomposition (rangeGrading R V) :=
  DirectSum.Decomposition.ofLinearMap _
    (DirectSum.toModule R ι _ fun i =>
      (DirectSum.lof R ι (fun i => rangeGrading R V i) i).comp
        (DirectSum.lof R ι V i).rangeRestrict)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.toModule_lof,
        LinearMap.id_apply]
      rfl)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      rintro ⟨x, y, rfl⟩
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.toModule_lof,
        LinearMap.id_apply]
      rfl)

/-- The inclusion of the `i`-th summand, cut down to its range, is bijective. -/
theorem rangeRestrict_lof_bijective (i : ι) :
    Function.Bijective (DirectSum.lof R ι V i).rangeRestrict := by
  refine ⟨(LinearMap.injective_rangeRestrict_iff _).2 fun a b hab ↦ ?_,
    LinearMap.surjective_rangeRestrict _⟩
  exact DirectSum.of_injective (β := V) i (by simpa only [DirectSum.lof_eq_of] using hab)

/-- The degree-`i` piece of `⨁ i, V i` is canonically `V i`. -/
noncomputable def rangeGradingEquiv (i : ι) : rangeGrading R V i ≃ₗ[R] V i :=
  (LinearEquiv.ofBijective _ (rangeRestrict_lof_bijective R V i)).symm

/-- `rangeGradingEquiv` undoes the inclusion of the `i`-th summand. -/
theorem rangeGradingEquiv_apply_of (i : ι) (x : V i) :
    rangeGradingEquiv R V i ⟨DirectSum.of V i x, ⟨x, DirectSum.lof_eq_of R ι V i x⟩⟩ = x :=
  (LinearEquiv.ofBijective _ (rangeRestrict_lof_bijective R V i)).symm_apply_eq.2
    (Subtype.ext (DirectSum.lof_eq_of R ι V i x).symm)

/-- `rangeGradingEquiv` reads off the unique summand representing a homogeneous element. -/
theorem rangeGradingEquiv_eq_of_coe_eq {i : ι} (z : rangeGrading R V i) (w : V i)
    (hz : (z : DirectSum ι V) = DirectSum.of V i w) : rangeGradingEquiv R V i z = w := by
  have hw : DirectSum.of V i w ∈ rangeGrading R V i := ⟨w, DirectSum.lof_eq_of R ι V i w⟩
  rw [show z = (⟨DirectSum.of V i w, hw⟩ : rangeGrading R V i) from Subtype.ext hz]
  exact rangeGradingEquiv_apply_of R V i w

variable {R V}

/-- Inclusions of heterogeneously equal elements into a direct sum agree. -/
theorem of_eq_of_heq {i j : ι} {a : V i} {b : V j} (e : i = j) (h : HEq a b) :
    DirectSum.of V i a = DirectSum.of V j b := by
  subst j
  cases h
  rfl

end DirectSum

namespace DirectSum

universe u

variable {R : Type u} [Semiring R] {ι : Type*} {V : ι → Type*} [DecidableEq ι]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- The inclusion of a summand commutes with `a - r • b`. -/
theorem of_sub_smul (i : ι) (a b : V i) (r : R) :
    DirectSum.of V i (a - r • b) = DirectSum.of V i a - r • DirectSum.of V i b := by
  simp only [← DirectSum.lof_eq_of R, map_sub, map_smul]

end DirectSum
